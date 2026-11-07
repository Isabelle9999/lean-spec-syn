-- proof check: one command, `lss_check_proof`, that turns proof text into a
-- verdict. every "proved" in the pipeline comes from one of its LSS_PROOF
-- warnings (a warning, same convention as wf_gate.lean's LSS_WF), never from the
-- absence of an error message.
--
-- the proof text is a string literal parsed here, not spliced into the file, so
-- it can only add theorems: a `set_option`, `axiom`, `#eval` or any other command
-- hidden in it is rejected before anything elaborates. each theorem elaborates
-- with:
--   debug.skipKernelTC false  the kernel checks the declaration at addDecl
--                             (Lean/AddDecl.lean:19-25 skips it when true);
--   Elab.async false          the proof and its kernel check finish inside
--                             elabCommand, so the verdict below reads a complete
--                             message log (Lean/Elab/MutualDef.lean:1238 would
--                             otherwise run a theorem body in a background task);
--   autoImplicit false        same reading of the statement as the gate.
-- after elaboration every declaration the text added is replayed through the
-- kernel from the environment before it (lssReplayOne, ported from Lean/Replay.lean,
-- what lean4checker runs): meta code inside a proof (`run_tac`, an elaborator) can
-- add a declaration with debug.skipKernelTC set for itself, and the option above
-- does not reach that. then `Lean.collectAxioms` (what `#print axioms` uses) must find only the three
-- standard axioms: sorryAx, `<decl>._native.*` (native_decide, decide +native,
-- bv_decide) and any declared axiom are rejected.
--
-- no Aeneas or Mathlib dependency (it needs only `Lean`, which both tracks
-- import): part of the crate environment on the rust track (lean.py builds it in
-- before aeneas_layer.lean), sent ahead of each check on the native track.
-- wf_gate.lean uses the two parsing helpers below, so this file always comes
-- before it.

open Lean Elab Command Parser in
/-- parse `text` as a sequence of top-level commands against `pmctx`, stopping at
end-of-input. never raises: a parse error becomes an error in the returned log. -/
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
/-- the axioms an accepted proof may depend on (`Classical.em` alone needs all three). -/
def lssAllowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

open Lean in
/-- why an axiom is not allowed, or `none` when it is. -/
def lssAxiomProblem (n : Name) : Option String :=
  if lssAllowedAxioms.contains n then none
  else if n == ``sorryAx then some "sorry"
  else if n.components.contains `_native then some "native"
  else some "axiom"

open Lean in
def lssProofMsg (nm : Name) (ok : Bool) (stage detail : String) (axioms : Array Name) : MessageData :=
  m!"LSS_PROOF {Json.compress (Json.mkObj [("name", Json.str (toString nm)), ("ok", Json.bool ok),
    ("stage", Json.str stage), ("detail", Json.str detail),
    ("axioms", Json.arr (axioms.map (fun a => Json.str (toString a))))])}"

open Lean in
/-- options every checked theorem elaborates under (see the header). -/
def lssProofOpts (opts : Options) (heartbeats : Option Nat) : Options :=
  let o := ((opts.setBool `debug.skipKernelTC false).setBool `Elab.async false).setBool `autoImplicit false
  match heartbeats with
  | some n => o.set `maxHeartbeats n
  | none => o

open Lean in
/-- add `n` (one of `news`) to the kernel environment again, after the declarations of
`news` it uses: Lean/Replay.lean's `replayConstant`, which that module's
`Environment.replay` (what lean4checker runs) calls, ported here because Lean.Replay is
not imported everywhere this file is (Mathlib does not import it, and importing it as
well would make a second base environment in a server). definitions, theorems,
opaques and axioms are re-added; unsafe and partial ones are skipped, as replay skips
them; an inductive type, constructor, recursor or quotient is an error, since neither
a theorem nor a helper definition adds one. -/
partial def lssReplayOne (news : Std.HashMap Name ConstantInfo) (n : Name) :
    StateT (Kernel.Environment × NameSet) IO Unit := do
  let some ci := news[n]? | return
  if (← get).2.contains n then return
  modify fun (env, seen) => (env, seen.insert n)
  if ci.isUnsafe || ci.isPartial then return
  for c in ci.getUsedConstantsAsSet do
    lssReplayOne news c
  let decl ← match ci with
    | .defnInfo v => pure (Declaration.defnDecl v)
    | .thmInfo v => pure (Declaration.thmDecl v)
    | .opaqueInfo v => pure (Declaration.opaqueDecl v)
    | .axiomInfo v => pure (Declaration.axiomDecl v)
    | _ => throw (IO.userError s!"'{n}' is an inductive type, constructor, recursor or quotient, which no theorem or helper definition adds")
  match (← get).1.addDeclCore 0 decl (cancelTk? := none) with
  | .ok env => modify fun (_, seen) => (env, seen)
  | .error ex => throw (IO.userError s!"while replaying declaration '{n}':\n{← (ex.toMessageData {}).toString}")

open Lean Elab Command in
/-- `none` when the kernel accepts again every declaration added since `env0`,
replayed from `env0` (lssReplayOne), else the kernel's error. -/
def lssReplaySince (env0 : Environment) : CommandElabM (Option String) := do
  let news := (← getEnv).constants.map₂.foldl
    (fun m n c => if env0.contains n then m else m.insert n c) ({} : Std.HashMap Name ConstantInfo)
  try
    liftCoreM (do
      let _ ← ((news.toList.map (·.1)).forM (lssReplayOne news) |>.run (env0.toKernelEnv, {}) : IO _)
      pure ())
    return none
  catch e => return some (← e.toMessageData.toString)

open Lean Elab Command in
/-- elaborate `cmds` (theorem declarations only) under `lssProofOpts` and log one
LSS_PROOF verdict for `fullName`. stages, in order: not_theorem, elab, missing,
replay, axioms, ok; a replay rejection also takes the text's declarations back out. the candidate's own messages go back into the log ahead of the
verdict, so repair prompts still see the error text. -/
def lssCheckCmds (cmds : Array Syntax) (fullName : Name) (heartbeats : Option Nat) : CommandElabM Unit := do
  let emit (ok : Bool) (stage detail : String) (axioms : Array Name := #[]) : CommandElabM Unit :=
    logWarning (lssProofMsg fullName ok stage detail axioms)
  for cmd in cmds do
    unless cmd.getKind == ``Parser.Command.declaration && cmd[1].getKind == ``Parser.Command.theorem do
      let kind := if cmd.getKind == ``Parser.Command.declaration then cmd[1].getKind else cmd.getKind
      emit false "not_theorem" s!"only theorem declarations are allowed, got `{kind}`"
      return
  let env0 ← getEnv
  let before := (← get).messages
  modify fun s => { s with messages := {} }
  withScope (fun sc => { sc with opts := lssProofOpts sc.opts heartbeats }) do
    for cmd in cmds do
      elabCommand cmd
  let log := (← get).messages
  modify fun s => { s with messages := before ++ log }
  if let some err ← lssFirstError log then
    emit false "elab" err
    return
  unless (← getEnv).contains fullName do
    emit false "missing" s!"no theorem `{fullName}` was added"
    return
  if let some why ← lssReplaySince env0 then
    setEnv env0
    emit false "replay" why
    return
  let axioms ← collectAxioms fullName
  let bad := axioms.filterMap (fun a => (lssAxiomProblem a).map (fun why => s!"{a} ({why})"))
  if bad.size > 0 then
    emit false "axioms" s!"not allowed: {bad.toList}" axioms
  else
    emit true "ok" "" axioms

open Lean Elab Command Parser in
/-- parse `text` against the current environment, namespace and opens. -/
def lssParseText (text : String) : CommandElabM (Array Syntax × MessageLog) := do
  let pmctx : ParserModuleContext :=
    { env := (← getEnv), options := (← getOptions), currNamespace := (← getCurrNamespace),
      openDecls := (← getOpenDecls) }
  return lssParseAll (mkInputContext text "<proof>") pmctx

open Lean Elab Command in
/-- `lss_check_proof "<theorems>" name:<n> heartbeats:<k>`: elaborate the
theorems in the string (helpers first, the theorem `n` among them) and log one
LSS_PROOF verdict for `n` (heartbeats:0 keeps the current maxHeartbeats); a
parse error is stage `parse`. -/
elab "lss_check_proof " src:str " name:" nmId:ident " heartbeats:" hb:num : command => do
  let ns ← getCurrNamespace
  let fullName := if ns.isAnonymous then nmId.getId else ns ++ nmId.getId
  let heartbeats := if hb.getNat == 0 then none else some hb.getNat
  let (cmds, parseLog) ← lssParseText src.getString
  if let some err ← lssFirstError parseLog then
    logWarning (lssProofMsg fullName false "parse" s!"proof text does not parse: {err}" #[])
    return
  lssCheckCmds cmds fullName heartbeats

open Lean Elab Command in
/-- `lss_define_helpers "<defs>"`: a Rust spec's helper definitions (synth.rust_helpers'
blocks, sent by lean.helpers_command without their `@[simp]`), checked as
lss_check_proof checks proof text. the string is parsed here, not spliced into the
file, so it can only add definitions: every command must be a `def lss_hp_…` with no
modifier (no attribute, docstring, `private`, `noncomputable`, `unsafe`, `partial`),
and anything else (`set_option`, `attribute`, `axiom`, `#eval`, `run_cmd`, a theorem)
is rejected before anything elaborates. each definition elaborates with
debug.skipKernelTC false and Elab.async false (as lssProofOpts sets them; autoImplicit
stays as the crate has it), so the kernel checks it, is replayed through the kernel as
lss_check_proof's text is, may depend only on the standard
axioms, and is then made a simp lemma, as Aeneas's tutorial tags its toList. every rejection is an
error and leaves the environment as it was before the command, every helper of the
text undefined, so a statement that uses a rejected helper never elaborates. only
errors are kept from the helpers' own messages. -/
elab "lss_define_helpers " src:str : command => do
  let (cmds, parseLog) ← lssParseText src.getString
  if let some err ← lssFirstError parseLog then
    throwError "LSS_HELPERS: the helper text does not parse: {err}"
  let mut names : Array Name := #[]
  for cmd in cmds do
    unless cmd.getKind == ``Parser.Command.declaration && cmd[1].getKind == ``Parser.Command.definition do
      let kind := if cmd.getKind == ``Parser.Command.declaration then cmd[1].getKind else cmd.getKind
      throwError "LSS_HELPERS: only definitions are allowed, got `{kind}`"
    unless cmd[0].getArgs.all (·.isNone) do
      throwError "LSS_HELPERS: a helper takes no modifier or attribute: {cmd[0]}"
    let id := cmd[1][1][0].getId
    unless id.isAtomic && (toString id).startsWith "lss_hp_" do
      throwError "LSS_HELPERS: a helper's name is `lss_hp_<name>_<hash>`, got `{id}`"
    names := names.push ((← getCurrNamespace) ++ id)
  let env0 ← getEnv
  let before := (← get).messages
  modify fun s => { s with messages := {} }
  withScope (fun sc => { sc with opts := (sc.opts.setBool `debug.skipKernelTC false).setBool `Elab.async false }) do
    for cmd in cmds do
      elabCommand cmd
  let log := (← get).messages
  -- only the errors go back into the log: a warning a helper's body logs could
  -- otherwise pass for a verdict (LSS_WF, LSS_PROOF) of the command after it
  let errs := log.toList.foldl (fun l m => if m.severity matches .error then l.add m else l) ({} : MessageLog)
  modify fun s => { s with messages := before ++ errs }
  if (← lssFirstError log).isSome then
    setEnv env0
    return
  if let some why ← lssReplaySince env0 then
    setEnv env0
    throwError "LSS_HELPERS: the kernel rejects a helper's declarations on replay: {why}"
  for n in names do
    unless (← getEnv).contains n do
      setEnv env0
      throwError "LSS_HELPERS: no definition `{n}` was added"
    let bad := (← collectAxioms n).filterMap (fun a => (lssAxiomProblem a).map (fun why => s!"{a} ({why})"))
    if bad.size > 0 then
      setEnv env0
      throwError "LSS_HELPERS: `{n}` depends on axioms that are not allowed: {bad.toList}"
  for n in names do
    elabCommand (← `(attribute [simp] $(mkIdent n):ident))
