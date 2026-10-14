-- well-formedness gate: one command, `lss_wf_gate`, that takes a candidate's full
-- theorem declaration as a string literal and checks it, in order, against six
-- named checks (one_theorem, is_theorem, no_attribute, conclusion_shape,
-- vocabulary, decidable), stopping at the first failure. each check reports one
-- LSS_WF {json} warning (a warning, since the server drops info messages), same
-- convention as aeneas_layer.lean's LSS_ATTEMPT/LSS_STEP/LSS_GOALS.
--
-- sent through the lean server the same way aeneas_layer.lean is: appended after
-- the crate text (rust track) or after `import Mathlib` + the lean-native source
-- (native track), fresh for every candidate -- nothing here is meant to persist
-- in the growing crate env, so python never saves the resulting env.
--
-- the candidate text is parsed independently (Parser.parseCommand, looped to
-- end-of-input) rather than spliced directly into the surrounding file, because
-- "exactly one theorem" has to see how many top-level commands the candidate
-- text itself contains -- splicing it in would just let Lean parse each one as
-- its own ordinary command, with no way for a later command to count them.
--
-- `lss_wf_gate` also takes an explicit `rust`/`native` track token (gate.py
-- passes it, matching the same track it picked its environment for): the rust
-- track only ever accepts the `spec`/`dspec` Hoare-triple conclusion, while the
-- native track additionally accepts the `∀ args, pre → P (f args)` shape by
-- finding where (if anywhere) the conclusion calls the unit.

-- this file has no Aeneas dependency (every Aeneas name it compares against is a
-- single-backtick *raw* `Name`, never resolved) so it compiles unchanged for the
-- lean-native track too; the Aeneas-only `Decidable` instances it also needs for
-- the rust track (Result/Error/ControlFlow/Vec/Slice) live in wf_gate_aeneas.lean,
-- sent alongside this file only for that track.

-- `Subtype` (Vec/Slice's own representation) has no Aeneas dependency either, so
-- it stays here rather than in wf_gate_aeneas.lean.
instance lssSubtypeDecEq {α} [DecidableEq α] (p : α → Prop) : DecidableEq (Subtype p) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

open Lean Elab Command Meta in
/-- is `callExpr` exactly `unitName` applied to pairwise-distinct members of `fvars`?
`MetaM` (rather than pure `Except`) only so a failing message can pretty-print the
offending subterm through `ppExpr` instead of `Expr`'s raw (hygiene-id-laden)
`ToString` instance. -/
def lssCheckCallShape (unitName : Name) (fvars : Array Expr) (callExpr : Expr) : MetaM (Except String Unit) := do
  let fn := callExpr.getAppFn
  let some cname := fn.constName?
    | return .error s!"program position is not a function call: {<- ppExpr callExpr}"
  if cname != unitName then
    return .error s!"program position calls `{cname}`, expected `{unitName}`"
  let args := callExpr.getAppArgs
  let mut seen : Array FVarId := #[]
  for a in args do
    let .fvar fvid := a
      | return .error s!"argument `{<- ppExpr a}` is not a bound variable"
    unless fvars.any (fun v => v.fvarId! == fvid) do
      return .error s!"argument `{<- ppExpr a}` is not one of the theorem's own bound variables"
    if seen.contains fvid then
      return .error s!"argument `{<- ppExpr a}` is used more than once"
    seen := seen.push fvid
  return .ok ()

open Lean Meta in
/-- every crate-manifest name used among `scanTerms` or in any hyp's type (the
rust track's `scanTerms` is just `#[post]`, a sibling of `progPos` under `spec`/
`dspec` rather than a subterm of it, so no exclusion is needed to begin with --
this alone is what catches a postcondition that merely repeats the call, `r = f x`
restated, or the whole body copied back in). -/
def lssForbiddenAmong (manifestNames : Array Name) (hyps scanTerms : Array Expr) :
    MetaM (Array Name) := do
  let mut consts : Array Name := #[]
  for t in scanTerms do
    consts := consts ++ t.getUsedConstants
  for h in hyps do
    consts := consts ++ (<- h.fvarId!.getType).getUsedConstants
  return consts.filter (fun n => manifestNames.contains n)

open Lean Meta in
/-- every crate-manifest name used in `scanRoot` (`core`) outside the subterm
`progPos`, excised via `Expr.replace`. `progPos` is the native track's one
*distinct* call to `unitName` (after `lssFindCalls`'s results are deduped by
value -- a second, genuinely different call is rejected before this is ever
reached). `Expr.replace` matching by value is therefore exactly the right
abstraction, not an approximation of it: every occurrence of that one value
*is* the program position, so excising all of them together is what "outside
the program position" is supposed to mean here. -/
def lssForbiddenOutside (manifestNames : Array Name) (progPos scanRoot : Expr) (hyps : Array Expr) :
    MetaM (Array Name) := do
  let placeholder <- mkFreshExprMVar (<- inferType progPos)
  let patched := scanRoot.replace (fun e => if e == progPos then some placeholder else none)
  lssForbiddenAmong manifestNames hyps #[patched]

open Lean in
/-- every occurrence of an application headed by `unitName` inside `e`. -/
partial def lssFindCalls (unitName : Name) (e : Expr) : Array Expr :=
  let here := if e.isApp && e.getAppFn.constName? == some unitName then #[e] else #[]
  let fromArgs := if e.isApp then e.getAppArgs.foldl (init := #[]) (fun acc a => acc ++ lssFindCalls unitName a) else #[]
  let fromBinder := match e with
    | .forallE _ d b _ => lssFindCalls unitName d ++ lssFindCalls unitName b
    | .lam _ d b _ => lssFindCalls unitName d ++ lssFindCalls unitName b
    | .letE _ t v b _ => lssFindCalls unitName t ++ lssFindCalls unitName v ++ lssFindCalls unitName b
    | .mdata _ b => lssFindCalls unitName b
    | _ => #[]
  here ++ fromArgs ++ fromBinder

open Lean Meta in
/-- is `Decidable e` found directly, or after unfolding *just* enough named defs
(one delta step at a time, stopping the moment an instance is found) to get
past a named precondition like `f_precond x` down to the `Prop` it actually
abbreviates (`x > 0`)? a plain `whnf`/`whnfD` over-unfolds: it keeps going
past `x > 0` itself, through `GT.gt`'s own instance projection, down to the
raw `Nat.le`/`Nat.lt` recursor -- which no longer matches the `Decidable`
instance registered for the `LT.lt`/`LE.le` *class method* it came from, so a
hypothesis that was perfectly decidable before unfolding looks undecidable
after. stepping one delta-unfold at a time and stopping as soon as
`synthInstance?` succeeds never reaches that far. -/
partial def lssDecidableAt (e : Expr) : MetaM Bool := do
  if (<- synthInstance? (mkApp (mkConst ``Decidable) e)).isSome then
    return true
  match <- unfoldDefinition? e (ignoreTransparency := true) with
  | some e' => lssDecidableAt e'
  | none => return false

open Lean Meta in
/-- `none` if every hyp and the postcondition (already applied to a fresh `r`) is
Decidable (via `lssDecidableAt`); else `some <subterm that failed>`, reported
using the original (unfolded) form so the message still matches what the
candidate wrote. -/
def lssDecidableProbe (hyps : Array Expr) (post : Expr) : MetaM (Option String) := do
  for h in hyps do
    let hty <- h.fvarId!.getType
    unless <- lssDecidableAt hty do
      return some s!"hypothesis `{<- ppExpr hty}` is not Decidable"
  unless <- lssDecidableAt post do
    return some s!"postcondition `{<- ppExpr post}` is not Decidable"
  return none

open Lean Elab Command Meta Parser in
/-- parse `text` as a sequence of top-level commands against `pmctx`, stopping at
end-of-input. never raises: a parse error becomes an error in the returned log
(and a possibly malformed command), which the caller reports as `one_theorem`. -/
partial def lssParseAll (ictx : InputContext) (pmctx : ParserModuleContext) : Array Syntax × MessageLog := Id.run do
  let mut mps : ModuleParserState := {}
  let mut messages : MessageLog := {}
  let mut acc : Array Syntax := #[]
  repeat
    let (stx, mps', messages') := parseCommand ictx pmctx mps messages
    mps := mps'
    messages := messages'
    if isTerminalCommand stx then
      break
    acc := acc.push stx
  return (acc, messages)

open Lean in
/-- text of the first error in `log`, if any. -/
def lssFirstError (log : MessageLog) : IO (Option String) := do
  match log.toList.find? (·.severity matches .error) with
  | some m => return some (← m.data.toString)
  | none => return none

open Lean in
/-- shared between the `CommandElabM` and `TermElabM` halves of `lss_wf_gate`:
`logWarning` itself is polymorphic over both (and `MetaM`), so this just builds
the message. -/
def lssWfMsg (check : String) (ok : Bool) (detail : String) : MessageData :=
  m!"LSS_WF {Json.compress (Json.mkObj [("gate", Json.str "wf"), ("check", Json.str check), ("ok", Json.bool ok), ("detail", Json.str detail)])}"

open Lean Elab Command Meta Parser in
elab "lss_wf_gate " src:str " unit:" unitId:ident " manifest:" "[" names:ident,* "]"
    divFlag:("allow_div" <|> "no_div") trackTok:("rust" <|> "native") : command => do
  let emit (check : String) (ok : Bool) (detail : String) : CommandElabM Unit :=
    logWarning (lssWfMsg check ok detail)
  let env <- getEnv
  let opts <- getOptions
  let ns <- getCurrNamespace
  let ods <- getOpenDecls
  let pmctx : ParserModuleContext := { env, options := opts, currNamespace := ns, openDecls := ods }
  let ictx := mkInputContext src.getString "<candidate>"
  let (cmds, parseLog) := lssParseAll ictx pmctx
  if let some err ← lssFirstError parseLog then
    emit "one_theorem" false s!"candidate does not parse: {err}"
    return
  if cmds.size != 1 then
    emit "one_theorem" false s!"expected exactly one top-level command, found {cmds.size}"
    return
  emit "one_theorem" true ""
  let cmd := cmds[0]!
  -- `is_theorem` before `no_attribute`: Mathlib's `lemma` isn't a `theorem` alt
  -- under `Command.declaration` at all (it macro-expands to one only later, at
  -- elaboration time) -- it has its own top-level syntax kind, so there is no
  -- `declModifiers` child to even look at until this has confirmed the shape.
  if cmd.getKind != ``Command.declaration then
    emit "is_theorem" false s!"expected a `theorem` declaration, got `{cmd.getKind}`"
    return
  let modifiersStx : TSyntax ``Command.declModifiers := ⟨cmd[0]⟩
  let altStx := cmd[1]
  if altStx.getKind != ``Command.theorem then
    emit "is_theorem" false s!"expected a `theorem` declaration, got `{altStx.getKind}`"
    return
  emit "is_theorem" true ""
  let mods? <- try some <$> liftTermElabM (elabModifiers modifiersStx)
               catch e => do
                 emit "no_attribute" false s!"could not read declaration modifiers: {<- e.toMessageData.toString}"
                 pure none
  let some mods := mods? | return
  if mods.attrs.size > 0 then
    emit "no_attribute" false s!"attribute(s) present: {mods.attrs.toList.map (fun a => toString a.name)}"
    return
  emit "no_attribute" true ""
  -- altStx is the `theorem` alt: `"theorem " >> recover declId ... >> declSig >> declVal`,
  -- so the keyword atom is child 0 and declId (itself `ident >> optional universes`) is child 1.
  let declIdStx := altStx[1]
  let shortName := declIdStx[0].getId
  let fullName := if ns.isAnonymous then shortName else ns ++ shortName
  -- `elabCommand` never throws: it logs every error (`withLogging`,
  -- Lean/Elab/Command.lean:459) and error recovery puts `sorry` in place of a
  -- failed subterm, so a candidate with a type error still adds its theorem. read
  -- the candidate's own messages instead, with `autoImplicit` off so an unknown
  -- name is an error rather than a new universally quantified variable.
  let before := (← get).messages
  modify fun s => { s with messages := {} }
  withScope (fun sc => { sc with opts := sc.opts.setBool `autoImplicit false }) (elabCommand cmd)
  let candLog := (← get).messages
  modify fun s => { s with messages := before ++ candLog }
  if let some err ← lssFirstError candLog then
    emit "conclusion_shape" false s!"statement does not elaborate: {err}"
    return
  let ci? <- try some <$> getConstInfo fullName
             catch e => do
               emit "conclusion_shape" false s!"could not find elaborated constant `{fullName}`: {<- e.toMessageData.toString}"
               pure none
  let some ci := ci? | return
  if ci.type.hasSorry then
    emit "conclusion_shape" false "the statement contains `sorry`"
    return
  -- the crate text is elaborated under `open <crate>`, so a bare `records.swap`
  -- (both `unit:` and every `manifest:` entry, exactly as callers already write
  -- them elsewhere, e.g. test_aeneas_layer.py) resolves to the fully-qualified
  -- `<crate>.records.swap` actually recorded on `Expr.const` applications --
  -- comparing against the unresolved short form would never match.
  let unitName? <- try some <$> resolveGlobalConstNoOverload unitId
                   catch e => do
                     emit "conclusion_shape" false s!"could not resolve unit `{unitId.getId}`: {<- e.toMessageData.toString}"
                     pure none
  let some unitName := unitName? | return
  -- a `<|>` of two string-literal parsers yields a `token.<lit>`-kinded node,
  -- not a plain atom -- `getAtomVal` is always empty here.
  let allowDiv := divFlag.raw.getKind == `token.allow_div
  let isRust := trackTok.raw.getKind == `token.rust
  let mut manifestNames <- names.getElems.mapM (fun n =>
    try resolveGlobalConstNoOverloadCore n.getId catch _ => pure n.getId)
  -- native track: the unit's auxiliaries (`where`/`let rec` helpers, `def f.aux`)
  -- are local constants named under the unit, so they are read from the
  -- environment rather than guessed from source text.
  unless isRust do
    manifestNames := (← getEnv).constants.foldStage2
      (fun acc n _ => if unitName.isPrefixOf n && !acc.contains n then acc.push n else acc) manifestNames
  liftTermElabM do
    let temit (check : String) (ok : Bool) (detail : String) : TermElabM Unit :=
      logWarning (lssWfMsg check ok detail)
    forallTelescope ci.type fun fvars core0 => do
      -- no `whnf`: `spec`/`dspec` are plain (reducible-unmarked) defs, and
      -- default-transparency whnf unfolds straight through them to `theta`'s
      -- stuck match, destroying the very shape this check looks for.
      let core <- instantiateMVars core0
      -- `spec`/`dspec` are `{α} (x : Result α) (p : Post α)`: arity 3 counting
      -- the implicit `α`, not 2 -- `isAppOfArity` counts every argument.
      -- single backtick (an unchecked raw `Name`, not a resolved one): this file
      -- is also sent for the lean-native track, which never imports Aeneas, so
      -- `` ``Aeneas.Std.WP.spec`` `` (resolved at compile time) would fail to
      -- elaborate there even on candidates that never take this branch.
      let isSpec := core.isAppOfArity `Aeneas.Std.WP.spec 3
      let isDspec := core.isAppOfArity `Aeneas.Std.WP.dspec 3
      let hyps <- fvars.filterM (fun fv => do isProp (<- fv.fvarId!.getType))
      if isSpec || isDspec then
        if isDspec && !allowDiv then
          temit "conclusion_shape" false "`⦃ ⦄div` (dspec) is only allowed for loop or recursive units"
        else
          let progPos := core.getArg! 1
          let post := core.getArg! 2
          match <- lssCheckCallShape unitName fvars progPos with
          | .error msg => temit "conclusion_shape" false msg
          | .ok () =>
            temit "conclusion_shape" true ""
            -- `post` is a sibling of `progPos` under `spec`/`dspec`, not one of
            -- its subterms, so scanning it directly (no exclusion needed) is
            -- exactly what catches a postcondition that merely restates the call
            -- (`r = f x`, or the whole body copied back in).
            let forbidden <- lssForbiddenAmong manifestNames hyps #[post]
            if forbidden.size > 0 then
              temit "vocabulary" false s!"forbidden crate name(s) used outside the program position: {forbidden.toList}"
            else
              temit "vocabulary" true ""
              let resTy <- whnf (<- inferType progPos)
              let alpha := resTy.appArg!
              let bad? <- withLocalDeclD `r alpha fun rFv => do
                lssDecidableProbe hyps (post.beta #[rFv])
              match bad? with
              | some msg => temit "decidable" false msg
              | none => temit "decidable" true ""
      else if isRust then
        -- the rust track only ever accepts the Hoare-triple conclusion; anything
        -- else (the old `= ok {...}` equation idiom included) is rejected here,
        -- before the native-only "which calls, how many" analysis below even runs.
        temit "conclusion_shape" false "conclusion must be `f args ⦃ r => P r ⦄`"
      else
        -- arguments and preconditions are the leading binders whose types do not
        -- call the unit; the conclusion starts at the first binder that does, so in
        -- `∀ x, pre x → ∀ i, i < (f x).1 → P` the `∀ i, ...` stays in the conclusion.
        let mut k := fvars.size
        for i in [0:fvars.size] do
          if (lssFindCalls unitName (← instantiateMVars (← fvars[i]!.fvarId!.getType))).size > 0 then
            k := i
            break
        let args := fvars.extract 0 k
        let argHyps <- args.filterM (fun fv => do isProp (<- fv.fvarId!.getType))
        let concl <- mkForallFVars (fvars.extract k fvars.size) core
        let calls := lssFindCalls unitName concl
        -- identical `Expr`s (literally the same call, occurring more than once --
        -- e.g. `(f x).1 < (f x).2`) count as one program position; only a second,
        -- genuinely *different* call is rejected.
        let distinct := calls.foldl (fun acc c => if acc.any (· == c) then acc else acc.push c) (#[] : Array Expr)
        if distinct.size == 0 then
          temit "conclusion_shape" false s!"the conclusion does not call `{unitName}`"
        else if distinct.size > 1 then
          let descs <- distinct.mapM (fun c => do let f <- ppExpr c; pure f)
          temit "conclusion_shape" false
            s!"the conclusion calls `{unitName}` with different arguments: {descs.toList}"
        else
          match <- lssCheckCallShape unitName args distinct[0]! with
          | .error msg => temit "conclusion_shape" false msg
          | .ok () =>
            temit "conclusion_shape" true ""
            let forbidden <- lssForbiddenOutside manifestNames distinct[0]! concl argHyps
            if forbidden.size > 0 then
              temit "vocabulary" false s!"forbidden crate name(s) used outside the program position: {forbidden.toList}"
            else
              temit "vocabulary" true ""
              let bad? <- lssDecidableProbe argHyps concl
              match bad? with
              | some msg => temit "decidable" false msg
              | none => temit "decidable" true ""
