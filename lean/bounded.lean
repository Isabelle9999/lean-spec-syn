-- bounded checking: run a candidate spec on concrete inputs before any prover.
--
-- sent once per crate, after wf_gate.lean and wf_gate_aeneas.lean, on the crate
-- env as built before the crate is opened ("env0", lean._aeneas_build_env); the
-- env this gives is the bounded check's own, never the one proofs run in, so the
-- instances below never change what a proof can use. every command is then sent
-- after `open <crate>`. no top-level open: each declaration opens only what it
-- needs, scoped to itself.
--
-- a candidate is read the way the gate reads it (autoImplicit off), so its
-- conclusion is `spec`/`dspec` of a call whose arguments are the statement's own
-- variables (the gate's conclusion_shape). generic statements are checked at one
-- instantiation (lssMono): a counterexample there refutes the statement for
-- every type, since it is universally quantified over its type and trait
-- arguments:
--   a type binder         the type of the crate's instance a trait binder is
--                         given, else Aeneas.Std.U32 (a parametric property
--                         is tested at one type with many values, as
--                         property-based testing of polymorphic code does);
--   a trait binder        the crate's own instance of that trait (a def the
--                         crate declares with that trait as its type; Aeneas
--                         marks the trait itself "Trait declaration");
--   a class binder        its synthesized instance;
--   a hypothesis on these alone (a "law": `∀ a b, OrdInst.cmp a b = ...`)
--                         proved for that instance, once, by lss_law_tac and the
--                         kernel; an instance that fails a law is never used.
-- the other binders are values. one that a hypothesis `x = e` defines (the
-- normal form python gives a call on a constructor, `l = List.Cons x tl`) takes
-- the value of `e`; every other value binder ("free") is sampled. a statement
-- none of this covers, or whose hypotheses or postcondition are not Decidable at
-- that instantiation, is "not evaluated" and goes on to the provers unchanged.
--
-- `lss_eval_plan <tag> crate:<C> stmt:"<stmt>"` reports what the check needs
--   from python: every binder's role, the free binders' types and the call's
--   result type (as type IR, see lssTypeIR), or why the statement is not
--   evaluated.
-- `lss_eval_spec <tag> crate:<C> stmt:"<stmt>" enc:"<fun v => ...>" rows:[[...], ...]`
--   evaluates it on rows of literals, one per free binder in binder order: the
--   hypotheses are then closed propositions, decided by evaluation (`discard`
--   when one is false), and the call is evaluated with the postcondition decided
--   on its `ok` value (`holds`/`violates`), or gives `fail` (with the error) or
--   `div`. the `ok` value comes back through `enc`. evaluation, not proof: a
--   refutation is checked separately through lss_check_proof.
-- `lss_eval_post <tag> crate:<C> stmt:"<stmt>" row:[...] outs:[...]` decides the
--   postcondition, at that row, on each given output instead of the real one
--   (the perturbation check: a spec that accepts every wrong output says nothing).
-- `lss_derive_deceq crate:<C>` gives every crate type DecidableEq, as the gate's
--   wf_gate_aeneas.lean does for Result: derived where Lean's handler can, and
--   for a nested inductive (a tree whose children are `Option (Node T)`, which
--   the handler does not cover) decided by its derived structural BEq at
--   evaluation time (lssDecEqViaBEq), which the kernel cannot reduce: such a
--   refutation can only be evaluation-only unless another tactic closes it.
-- every message is one LSS_EVAL warning (warning, as LSS_PROOF/LSS_WF).

/-- one evaluated run, as text python splits on the first tab: the outcome, then
the encoded `ok` value or the `fail` error. -/
def lssOutcome {α : Type u} (m : Aeneas.Std.Result α) (p : α → Bool) (enc : α → String) : String :=
  match m with
  | .ok r => (if p r then "holds\t" else "violates\t") ++ enc r
  | .fail e => "fail\t" ++ toString (repr e)
  | .div => "div\t"

open Lean Meta in
unsafe def lssEvalStringUnsafe (e : Expr) : MetaM String := evalExpr String (mkConst ``String) e

open Lean Meta in
@[implemented_by lssEvalStringUnsafe] opaque lssEvalString (e : Expr) : MetaM String

unsafe def lssDecEqViaBEqImpl {α : Type u} [BEq α] : DecidableEq α :=
  fun a b => if a == b then .isTrue lcProof else .isFalse lcProof

instance lssDecEqNonempty {α : Type u} : Nonempty (DecidableEq α) :=
  ⟨fun a b => Classical.propDecidable (a = b)⟩

/-- equality decided by `==`, for the crate types whose DecidableEq Lean cannot
derive: only ever instantiated (lss_derive_deceq) at a BEq derived from the
type's own constructors, structural and so agreeing with `=`; opaque, so the
logic never sees anything but some decision procedure. -/
@[implemented_by lssDecEqViaBEqImpl]
opaque lssDecEqViaBEq {α : Type u} [BEq α] : DecidableEq α

-- Aeneas's Vec and Array are subtypes of List, as Slice is; Aeneas gives Slice
-- DecidableEq this way (Aeneas/Std/Slice.lean) and the other two none, so a
-- postcondition `r = v` on a vector decides here as one on a slice does.
instance lssVecDecEq {α : Type u} [DecidableEq α] : DecidableEq (Aeneas.Std.alloc.vec.Vec α) :=
  inferInstanceAs (DecidableEq { _l : List α // _ })

instance lssArrayDecEq {α : Type u} [DecidableEq α] {n : Aeneas.Std.Usize} : DecidableEq (Aeneas.Std.Array α n) :=
  inferInstanceAs (DecidableEq { _l : List α // _ })

open Lean Meta in
/-- would deciding with this instance enumerate a whole type (a quantifier over a
Fintype)? the check samples inputs; it never enumerates one. -/
def lssEnumerates (inst : Expr) : Bool :=
  inst.getUsedConstants.any fun n =>
    (`Fintype).isPrefixOf n || (`Finset).isPrefixOf n || (`Multiset).isPrefixOf n

open Lean Meta in
/-- `decide e`, unfolding one named definition at a time until an instance is
found (as the gate's `lssDecidableAt`, so a named precondition decides). -/
partial def lssMkDecide (e : Expr) : MetaM Expr := do
  if let some inst ← synthInstance? (mkApp (mkConst ``Decidable) e) then
    if lssEnumerates inst then
      throwError "not Decidable without enumerating a whole type: {e}"
    return mkApp2 (mkConst ``Decidable.decide) e inst
  match ← unfoldDefinition? e (ignoreTransparency := true) with
  | some e' => lssMkDecide e'
  | none => throwError "not Decidable: {e}"

open Lean Meta in
def lssEvalBool (b : Expr) : MetaM Bool := do
  return (← lssEvalString (← mkAppM ``toString #[b])) == "true"

open Lean Elab Term Meta in
/-- parse and elaborate `s`, against `ty` when given, with no auto-bound names
and no error recovery. -/
def lssElabString (s : String) (ty : Option Expr) : TermElabM Expr := do
  let stx ← match Parser.runParserCategory (← getEnv) `term s with
    | .ok stx => pure stx
    | .error e => throwError "does not parse: {e}"
  let e ← withoutAutoBoundImplicit <| withoutErrToSorry do
    let e ← match ty with
      | some t => elabTermEnsuringType stx t
      | none => elabType stx
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  if e.hasMVar || e.hasSorry then throwError "does not elaborate: {s}"
  return e

open Lean Meta in
/-- `e` printed with full names, so python can read it back under any `open`. -/
def lssText (e : Expr) : MetaM String := do
  if let some n := e.constName? then return toString n
  let fmt ← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr e)
  return toString fmt

open Lean Meta in
/-- is `n` a trait Aeneas translated (its declaration's doc comment says so)? -/
def lssIsTrait (n : Name) : MetaM Bool := do
  match ← findDocString? (← getEnv) n with
  | some d => return (d.dropWhile Char.isWhitespace).startsWith "Trait declaration"
  | none => return false

open Lean Meta in
/-- the crate's own instances of `trait`: closed defs under the crate's namespace
whose type is `trait` applied to something, by name. -/
def lssCrateInstances (crate trait : Name) : MetaM (Array Name) := do
  let found := (← getEnv).constants.foldStage2 (fun (acc : Array Name) n ci =>
    match ci with
    | .defnInfo d =>
      if crate.isPrefixOf n && d.levelParams.isEmpty && !d.type.isForall
          && d.type.getAppFn.constName? == some trait then acc.push n else acc
    | _ => acc) #[]
  return found.qsort (fun a b => a.toString < b.toString)

/-- what one binder of a candidate statement is given: see the file header. -/
inductive LssRole where
  | type | inst | cls | law | hyp | defn | free (i : Nat) | det (rhs : Lean.Expr)
deriving Inhabited

open Lean Elab Term Meta in
/-- the statement at one instantiation of its type, trait and class binders
(see the file header): the statement with those binders removed, and for every
binder of the original, in order, `some` description of what it was given or
`none` for one that stays. throws `not evaluated: ...`. -/
def lssMono (crate : Name) (stmt : Expr) : TermElabM (Expr × Array (Option Json) × Array Name) :=
  forallTelescope stmt fun xs core => do
    let mut vals := xs
    let mut roles : Array (Option Json) := xs.map fun _ => none
    let mut types : Array Nat := #[]
    for i in [:xs.size] do
      let ty ← inferType xs[i]!
      if (← whnf ty).isSort then
        vals := vals.set! i (← mkFreshExprMVar ty)
        types := types.push i
    let mut insts := #[]
    for i in [:xs.size] do
      if types.contains i then continue
      let ty ← instantiateMVars ((← inferType xs[i]!).replaceFVars xs vals)
      let some tn := ty.getAppFn.constName? | continue
      unless ← lssIsTrait tn do continue
      let mut found := none
      for c in ← lssCrateInstances crate tn do
        if ← isDefEq ty (← getConstInfo c).type then
          found := some c
          break
      let some c := found
        | throwError "not evaluated: the crate has no instance of {tn}"
      vals := vals.set! i (mkConst c)
      roles := roles.set! i (some (Json.mkObj [("k", "inst"), ("v", Json.str (toString c)),
        ("name", Json.str (toString (← xs[i]!.fvarId!.getUserName)))]))
      insts := insts.push c
    for i in types do
      let m := vals[i]!
      unless ← m.mvarId!.isAssigned do
        unless ← isDefEq (← inferType m) (mkSort Level.one) do
          throwError "not evaluated: type binder {xs[i]!} is not a `Type`"
        unless ← isDefEq m (mkConst ``Aeneas.Std.U32) do
          throwError "not evaluated: cannot instantiate {xs[i]!}"
      roles := roles.set! i (some (Json.mkObj [("k", "type"), ("v", Json.str (← lssText (← instantiateMVars m))),
        ("name", Json.str (toString (← xs[i]!.fvarId!.getUserName)))]))
    for i in [:xs.size] do
      if roles[i]!.isSome then continue
      let ty ← instantiateMVars ((← inferType xs[i]!).replaceFVars xs vals)
      if (← isClass? ty).isSome then
        if ty.hasFVar then
          throwError "not evaluated: class binder {xs[i]!} depends on a value"
        let some v ← synthInstance? ty
          | throwError "not evaluated: no instance of {ty}"
        vals := vals.set! i v
        roles := roles.set! i (some (Json.mkObj [("k", "class")]))
    let keep := (Array.range xs.size).filter (fun i => roles[i]!.isNone) |>.map (xs[·]!)
    let body ← mkForallFVars keep core
    let stmt' ← instantiateMVars (body.replaceFVars xs vals)
    if stmt'.hasMVar then throwError "not evaluated: the instantiation is not determined"
    return (stmt', roles, insts)

/-- a statement at one instantiation, opened: its binders, their roles, the
order the value binders get values in, the call and the postcondition. -/
structure LssShape where
  ys : Array Lean.Expr
  roles : Array LssRole
  order : Array Nat
  nfree : Nat
  prog : Lean.Expr
  post : Lean.Expr
  isDspec : Bool

open Lean Elab Term Meta in
/-- open the instantiated statement and give every binder its role. -/
def lssShapeOf {β} (stmt : Expr) (k : LssShape → TermElabM β) : TermElabM β :=
  forallTelescope stmt fun ys core => do
    let isSpec := core.isAppOfArity ``Aeneas.Std.WP.spec 3
    let isDspec := core.isAppOfArity ``Aeneas.Std.WP.dspec 3
    unless isSpec || isDspec do throwError "the conclusion is not a Hoare triple"
    let n := ys.size
    let isP ← ys.mapM fun y => do isProp (← inferType y)
    -- a value binder that a later hypothesis `y = e` (or `e = y`) defines, and
    -- which hypothesis defines it
    let mut rhs : Array (Option (Expr × Nat)) := ys.map fun _ => none
    for j in [:n] do
      unless isP[j]! do continue
      let some (_, a, b) := (← instantiateMVars (← inferType ys[j]!)).eq? | continue
      for (l, r) in [(a, b), (b, a)] do
        if let some i := ys.findIdx? (· == l) then
          if i < j && !isP[i]! && rhs[i]!.isNone && !r.containsFVar l.fvarId! then
            rhs := rhs.set! i (some (r, j))
            break
    -- the order values are computed in: a sampled binder once its type's
    -- binders have values, a defined one once its `e`'s have. when that stalls
    -- (`e` uses a hypothesis, or definitions form a cycle), one defined binder
    -- is sampled instead and its hypothesis decided like any other.
    let fvarsIn (e : Expr) : Array Nat := (Array.range n).filter fun i => e.containsFVar ys[i]!.fvarId!
    let mut ready : Array Bool := ys.map fun _ => false
    let mut order : Array Nat := #[]
    let mut again := true
    while again do
      again := false
      let mut progress := true
      while progress do
        progress := false
        for i in [:n] do
          if isP[i]! || ready[i]! then continue
          let deps ← match rhs[i]! with
            | some (e, _) => pure (fvarsIn e)
            | none => pure (fvarsIn (← inferType ys[i]!))
          if deps.all (fun d => ready[d]!) then
            ready := ready.set! i true
            order := order.push i
            progress := true
      if let some i := (Array.range n).find? (fun i => !isP[i]! && !ready[i]! && rhs[i]!.isSome) then
        rhs := rhs.set! i none
        again := true
    unless (Array.range n).all (fun i => isP[i]! || ready[i]!) do
      throwError "not evaluated: the binders' types depend on each other in a way no sampling order meets"
    let defining := (Array.range n).filterMap fun i => rhs[i]!.map (·.2)
    let mut roles := #[]
    let mut nfree := 0
    for i in [:n] do
      if isP[i]! then
        let ty ← inferType ys[i]!
        -- a defining hypothesis holds by construction: it is never decided
        roles := roles.push (if defining.contains i then .defn
          else if ys.any (fun y => ty.containsFVar y.fvarId!) then .hyp else .law)
      else match rhs[i]! with
        | some (e, _) => roles := roles.push (.det e)
        | none =>
          roles := roles.push (.free nfree)
          nfree := nfree + 1
    k { ys, roles, order, nfree, prog := core.getArg! 1, post := core.getArg! 2, isDspec }

open Lean Elab Term Meta in
/-- values for the value binders from one row of literals (one per free binder),
as the `(binders, values)` to substitute. -/
def lssRowValues (sh : LssShape) (lits : Array String) : TermElabM (Array Expr × Array Expr) := do
  unless lits.size == sh.nfree do
    throwError "expected {sh.nfree} values, got {lits.size}"
  let mut src := #[]
  let mut dst := #[]
  for i in sh.order do
    let v ← match sh.roles[i]! with
      | .free k => do
        let ty := (← inferType sh.ys[i]!).replaceFVars src dst
        if ty.hasFVar then throwError "the type of a sampled binder depends on a hypothesis"
        lssElabString lits[k]! (some ty)
      | .det e => do
        let v := e.replaceFVars src dst
        if v.hasFVar then throwError "a defined binder depends on a hypothesis"
        pure v
      | _ => throwError "not a value binder"
    src := src.push sh.ys[i]!
    dst := dst.push v
  return (src, dst)

open Lean Elab Term Meta in
/-- `(call, α, fun r => decide (P r))` at these values. -/
def lssPostAt (sh : LssShape) (src dst : Array Expr) : TermElabM (Expr × Expr × Expr) := do
  let m := sh.prog.replaceFVars src dst
  let p := sh.post.replaceFVars src dst
  if m.hasFVar || p.hasFVar then throwError "the call or postcondition depends on a hypothesis"
  let α := (← whnf (← inferType m)).appArg!
  let pb ← withLocalDeclD `r α fun r => do mkLambdaFVars #[r] (← lssMkDecide (p.beta #[r]))
  return (m, α, pb)

open Lean Meta in
/-- the type IR python's samplers, literals and encoders use
(tools/translation_check.py), read off the type itself: scalars, Bool, Unit,
tuples, Option, Array, Slice, Vec, and the crate's own structures and
inductives at their arguments, `["self"]` marking where an inductive contains
itself (through Option or directly). throws on anything else (a function, as in
a backward function's result). -/
partial def lssTypeIR (crate : Name) (stack : Array Expr) (ty : Expr) : MetaM Json := do
  let ty ← instantiateMVars ty
  if let some top := stack.back? then
    if ← withReducible (isDefEq ty top) then return Json.arr #["self"]
  for s in stack do
    if ← withReducible (isDefEq ty s) then throwError "mutually recursive type {ty}"
  let scalars : List String := ["U8", "U16", "U32", "U64", "U128", "Usize",
    "I8", "I16", "I32", "I64", "I128", "Isize"]
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  let some c := fn.constName? | throwError "type {ty} is not supported"
  if let .str (.str (.str .anonymous "Aeneas") "Std") s := c then
    if scalars.contains s then return Json.arr #["int", Json.str ("Std." ++ s)]
  if c == ``Bool then return Json.arr #["bool"]
  if c == ``Unit || c == ``PUnit then return Json.arr #["tuple", Json.arr #[]]
  if c == ``Prod then
    -- `A × B × C` is right-nested; python's tuples are flat
    let mut elems := #[← lssTypeIR crate stack args[0]!]
    let mut rest := args[1]!
    while rest.isAppOfArity ``Prod 2 do
      elems := elems.push (← lssTypeIR crate stack rest.appFn!.appArg!)
      rest := rest.appArg!
    elems := elems.push (← lssTypeIR crate stack rest)
    return Json.arr #["tuple", Json.arr elems]
  if c == ``Option then return Json.arr #["option", ← lssTypeIR crate stack args[0]!]
  if c == `Aeneas.Std.Slice then return Json.arr #["slice", ← lssTypeIR crate stack args[0]!]
  if c == `Aeneas.Std.alloc.vec.Vec then return Json.arr #["vec", ← lssTypeIR crate stack args[0]!]
  if c == `Aeneas.Std.Array then
    -- the length, evaluated: `8#usize` prints differently under different options
    let len ← lssEvalString (← mkAppM ``toString #[← mkAppM ``Aeneas.Std.UScalar.val #[args[1]!]])
    return Json.arr #["array", ← lssTypeIR crate stack args[0]!, Json.str len]
  let env ← getEnv
  let some (.inductInfo info) := env.find? c | throwError "type {ty} is not supported"
  unless crate.isPrefixOf c && info.numIndices == 0 && args.size == info.numParams do
    throwError "type {ty} is not supported"
  let params := args.extract 0 info.numParams
  let stack := stack.push ty
  let fieldTypes (ctor : Name) : MetaM (Array Json) := do
    let cty ← instantiateForall (← getConstInfo ctor).type params
    forallTelescope cty fun fs _ => fs.mapM fun f => do lssTypeIR crate stack (← inferType f)
  let tyText ← lssText ty
  if isStructure env c then
    let fields := getStructureFields env c
    let tys ← fieldTypes info.ctors[0]!
    return Json.arr #["struct", Json.str (toString c),
      Json.arr ((fields.zip tys).map fun (f, t) => Json.arr #[Json.str (toString f), t]), Json.str tyText]
  let variants ← info.ctors.toArray.mapM fun ctor => do
    let short := match ctor with
      | .str _ s => s
      | _ => toString ctor
    return Json.arr #[Json.str short, Json.arr (← fieldTypes ctor)]
  return Json.arr #["enum", Json.str (toString c), Json.arr variants, Json.str tyText]

open Lean Meta in
/-- the crate-local definitions a law about these instances unfolds to: the
instances, what their values use from the crate (their method bodies), and the
trait's projections, to a small depth. -/
def lssLawUnfolds (crate : Name) (insts : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := insts
  let mut frontier := insts
  for _ in [0:3] do
    let mut next := #[]
    for n in frontier do
      if let some (.defnInfo d) := env.find? n then
        for c in d.value.getUsedConstants ++ d.type.getUsedConstants do
          if crate.isPrefixOf c && !out.contains c then
            if (env.find? c).any (·.isDefinition) || (env.getProjectionFnInfo? c).isSome then
              out := out.push c
              next := next.push c
    frontier := next
  for n in insts do
    if let some tn := (← getConstInfo n).type.getAppFn.constName? then
      if isStructure env tn then
        for f in getStructureFields env tn do
          if let some p := getProjFnForField? env tn f then
            unless out.contains p do out := out.push p
  return out

/-- the tactics a law is tried with, after its instances are unfolded: what
Aeneas's own proofs of such laws do (tests/lean/Avl/ScalarOrder.lean: unfold the
instance, split the method's `if`s, close each case by simp or scalar_tac), then
grind. -/
macro "lss_law_portfolio" : tactic =>
  `(tactic| first
    | (intros; (try dsimp only at *); grind)
    | (intros; (try dsimp only at *); (repeat' split) <;> first | rfl | (simp_all; done) | scalar_tac | grind)
    | decide)

open Lean Elab Tactic Meta in
/-- `lss_law_tac [I₁, ...]`: unfold these crate instances (lssLawUnfolds) in the
goal, then lss_law_portfolio. the refutation of a statement with laws proves
them with this, as lss_eval_plan did. -/
elab "lss_law_tac " "[" insts:ident,* "]" : tactic => do
  let names ← insts.getElems.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
  let crate := match names[0]? with
    | some n => n.getRoot
    | none => .anonymous
  let unfolds ← lssLawUnfolds crate names
  let g ← getMainGoal
  let t ← g.getType
  let t' ← deltaExpand t (unfolds.contains ·)
  replaceMainGoal [← g.replaceTargetDefEq t']
  evalTactic (← `(tactic| lss_law_portfolio))

open Lean Elab Term Meta in
/-- prove the closed law `ty` for these instances, by lss_law_tac and the
kernel, axioms audited as every proof is (proof_check.lean). -/
def lssProveLaw (insts : Array Name) (ty : Expr) : TermElabM (Option String) := do
  let tac := "by lss_law_tac [" ++ ", ".intercalate (insts.toList.map toString) ++ "]"
  -- a failing tactic logs its error as well as throwing: keep the log as it was
  let msgs := (← getThe Core.State).messages
  try
    let pf ← lssElabString tac (some ty)
    withoutModifyingEnv do
      let nm ← mkFreshUserName `lssLaw
      -- positional (mkTheoremValEx): Aeneas makes `name` a keyword, so `{ name := .. }` does not parse
      addDecl (.thmDecl (mkTheoremValEx nm [] ty pf []))
      for a in ← collectAxioms nm do
        if let some why := lssAxiomProblem a then return some why
      return none
  catch e =>
    let why ← e.toMessageData.toString
    modifyThe Core.State fun st => { st with messages := msgs }
    return some why

open Lean in
def lssEvalMsg (fields : List (String × Json)) : MessageData :=
  m!"LSS_EVAL {Json.compress (Json.mkObj fields)}"

syntax lssStrList := "[" str,* "]"

open Lean in
def lssStrings (l : TSyntax `lssStrList) : Array String :=
  l.raw[1].getSepArgs.map (·.isStrLit?.getD "")

open Lean Elab Command Term Meta in
/-- run `k` on the statement at its instantiation, its shape, the original
binders' roles and the instances used; any error becomes an `ok: false`
LSS_EVAL message (python reads a `not evaluated:` detail as that verdict). -/
def lssWithStatement (tag : Ident) (crate : Ident) (s : String)
    (k : LssShape → Array (Option Json) → Array Name → TermElabM (List (String × Json))) : CommandElabM Unit := do
  let tagJ := ("tag", Json.str (toString tag.getId))
  try
    let fields ← liftTermElabM do
      let stmt ← lssElabString s none
      let (stmt', roles, insts) ← lssMono crate.getId stmt
      lssShapeOf stmt' fun sh => k sh roles insts
    logWarning (lssEvalMsg (tagJ :: ("ok", true) :: fields))
  catch e =>
    logWarning (lssEvalMsg [tagJ, ("ok", false), ("detail", Json.str (← e.toMessageData.toString))])

open Lean in
/-- every original binder's role, for the refutation python writes: the kept
binders' roles fill the `none`s in order. -/
def lssBinderRoles (sh : LssShape) (mono : Array (Option Json)) : Array Json := Id.run do
  let mut out := #[]
  let mut j := 0
  for r in mono do
    match r with
    | some d => out := out.push d
    | none =>
      let d := match sh.roles[j]! with
        | .free i => Json.mkObj [("k", "arg"), ("i", Json.num i)]
        | .det _ => Json.mkObj [("k", "det")]
        | .hyp | .defn => Json.mkObj [("k", "hyp")]
        | .law => Json.mkObj [("k", "law")]
        | _ => Json.mkObj [("k", "?")]
      out := out.push d
      j := j + 1
  return out

open Lean Elab Command Term Meta in
elab "lss_eval_plan " tag:ident " crate:" crateId:ident " stmt:" s:str : command =>
  lssWithStatement tag crateId s.getString fun sh mono insts => do
    -- laws first: an instance that fails one is never evaluated at
    for i in [:sh.ys.size] do
      if let .law := sh.roles[i]! then
        let ty ← instantiateMVars (← inferType sh.ys[i]!)
        if let some why ← lssProveLaw insts ty then
          throwError "not evaluated: the crate's instance does not meet the hypothesis `{ty}` (no proof: {why})"
    -- decidable at this instantiation (as the gate's lssDecidableProbe, after it)
    for i in [:sh.ys.size] do
      if let .hyp := sh.roles[i]! then
        let ty ← inferType sh.ys[i]!
        try discard <| lssMkDecide ty
        catch e => throwError "not evaluated: hypothesis `{ty}`: {e.toMessageData}"
    let α := (← whnf (← inferType sh.prog)).appArg!
    withLocalDeclD `r α fun r => do
      try discard <| lssMkDecide (sh.post.beta #[r])
      catch e => throwError "not evaluated: postcondition: {e.toMessageData}"
    let ir (ty : Expr) : TermElabM Json := do
      try lssTypeIR crateId.getId #[] ty
      catch e => pure (Json.mkObj [("unsupported", Json.str (← e.toMessageData.toString))])
    let mut free := #[]
    for i in [:sh.ys.size] do
      if let .free _ := sh.roles[i]! then
        let ty ← inferType sh.ys[i]!
        free := free.push (Json.mkObj [("name", Json.str (toString (← sh.ys[i]!.fvarId!.getUserName))),
          ("type", Json.str (← lssText ty)), ("ir", ← ir ty)])
    let ret ← ir α
    return [("kind", Json.str (if sh.isDspec then "dspec" else "spec")),
            ("binders", Json.arr (lssBinderRoles sh mono)), ("free", Json.arr free), ("ret", ret),
            ("insts", Json.arr (insts.map (Json.str ∘ toString)))]

open Lean Elab Command Term Meta in
elab "lss_eval_spec " tag:ident " crate:" crateId:ident " stmt:" s:str " enc:" enc:str
    " rows:[" rows:lssStrList,* "]" : command =>
  lssWithStatement tag crateId s.getString fun sh _ _ => do
    let rows := rows.getElems.map lssStrings
    let mut out := #[]
    for lits in rows do
      let row ← try
        let (src, dst) ← lssRowValues sh lits
        let mut discard := false
        for i in [:sh.ys.size] do
          if let .hyp := sh.roles[i]! then
            let hty := (← inferType sh.ys[i]!).replaceFVars src dst
            if hty.hasFVar then throwError "a hypothesis depends on another hypothesis"
            unless ← lssEvalBool (← lssMkDecide hty) do
              discard := true
              break
        if discard then
          pure (Json.mkObj [("outcome", "discard")])
        else
          let (m, α, pb) ← lssPostAt sh src dst
          let encFn ← lssElabString enc.getString (some (← mkArrow α (mkConst ``String)))
          let txt ← lssEvalString (← mkAppM ``lssOutcome #[m, pb, encFn])
          let (o, v) := match txt.splitOn "\t" with
            | o :: rest => (o, "\t".intercalate rest)
            | [] => ("error", "")
          pure (Json.mkObj [("outcome", Json.str o), ("value", Json.str v)])
      catch e => pure (Json.mkObj [("outcome", "error"), ("detail", Json.str (← e.toMessageData.toString))])
      out := out.push row
    return [("kind", Json.str (if sh.isDspec then "dspec" else "spec")), ("rows", Json.arr out)]

open Lean Elab Command Term Meta in
elab "lss_eval_post " tag:ident " crate:" crateId:ident " stmt:" s:str " row:" row:lssStrList
    " outs:" outs:lssStrList : command =>
  lssWithStatement tag crateId s.getString fun sh _ _ => do
    let (src, dst) ← lssRowValues sh (lssStrings row)
    let (_, α, pb) ← lssPostAt sh src dst
    let mut out := #[]
    for o in lssStrings outs do
      let r ← try
        let v ← lssElabString o (some α)
        pure (Json.str (if ← lssEvalBool (pb.beta #[v]) then "holds" else "violates"))
      catch _ => pure (Json.str "error")
      out := out.push r
    return [("outs", Json.arr out)]

open Lean Meta in
/-- does `c` (applied to fresh params, each type param with DecidableEq) have a
DecidableEq instance already? -/
def lssHasDecEq (c : Name) : MetaM Bool := do
  let info ← getConstInfoInduct c
  forallTelescope info.type fun ps _ => do
    let tps ← ps.filterM fun p => do return (← whnf (← inferType p)).isSort
    let rec go (i : Nat) : MetaM Bool := do
      if h : i < tps.size then
        withLocalDecl `inst .instImplicit (← mkAppM ``DecidableEq #[tps[i]]) fun _ => go (i + 1)
      else
        return (← synthInstance? (← mkAppM ``DecidableEq #[mkAppN (mkConst c) ps])).isSome
    go 0

open Lean Meta in
/-- add `instance : ∀ params [DecidableEq T]..., DecidableEq (c params)` decided
by c's derived BEq (lssDecEqViaBEq). -/
def lssAddDecEqViaBEq (c : Name) : MetaM Unit := do
  let info ← getConstInfoInduct c
  forallTelescope info.type fun ps _ => do
    let tps ← ps.filterM fun p => do return (← whnf (← inferType p)).isSort
    let rec go (i : Nat) (locals : Array Expr) : MetaM Unit := do
      if h : i < tps.size then
        withLocalDecl `inst .instImplicit (← mkAppM ``DecidableEq #[tps[i]]) fun x => go (i + 1) (locals.push x)
      else
        let tyApp := mkAppN (mkConst c) ps
        let beq ← synthInstance (← mkAppM ``BEq #[tyApp])
        let lvl ← getLevel tyApp
        let val := mkApp2 (mkConst ``lssDecEqViaBEq [lvl.dec.getD Level.zero]) tyApp beq
        let ty ← mkAppM ``DecidableEq #[tyApp]
        let nm := c ++ `lssDecEqViaBEq
        addAndCompile (.defnDecl (mkDefinitionValEx nm [] (← mkForallFVars (ps ++ locals) ty)
          (← mkLambdaFVars (ps ++ locals) val) .abbrev .safe []))
        setReducibleAttribute nm
        addInstance nm .global 100
    go 0 #[]

open Lean Elab Command Meta in
/-- elaborate `cmd`, reporting whether it logged an error (its messages are dropped). -/
def lssTryCommand (cmd : Syntax) : CommandElabM Bool := do
  let before := (← get).messages
  modify fun s => { s with messages := {} }
  elabCommand cmd
  let log := (← get).messages
  modify fun s => { s with messages := before }
  return !log.hasErrors

open Lean Elab Command Meta in
elab "lss_derive_deceq " "crate:" crateId:ident : command => do
  let crateName := crateId.getId
  let env ← getEnv
  let mut todo := #[]
  for (n, ci) in env.constants.map₂.toList do
    if let .inductInfo info := ci then
      if crateName.isPrefixOf n && info.numIndices == 0 && info.levelParams.isEmpty then
        let isTrait ← liftTermElabM (lssIsTrait n)
        let isPropTy ← liftTermElabM <| forallTelescope info.type fun _ s => pure s.isProp
        unless isTrait || isPropTy do todo := todo.push n
  todo := todo.qsort (fun a b => a.toString < b.toString)
  let mut derived := #[]
  let mut viaBEq := #[]
  -- a type's DecidableEq can need another's first: retry until nothing changes
  let mut progress := true
  while progress do
    progress := false
    let mut left := #[]
    for n in todo do
      if ← liftTermElabM (lssHasDecEq n) then
        progress := true
        continue
      let okCmd ← lssTryCommand (← `(command| deriving instance DecidableEq for $(mkIdent n)))
      if okCmd then
        derived := derived.push n
        progress := true
      else left := left.push n
    todo := left
    unless progress do
      -- the derive handler does not cover nested inductives: decide those by BEq
      for n in todo do
        if ← lssTryCommand (← `(command| deriving instance BEq for $(mkIdent n))) then
          try
            liftTermElabM (lssAddDecEqViaBEq n)
            viaBEq := viaBEq.push n
            progress := true
          catch _ => pure ()
      todo := todo.filter (!viaBEq.contains ·)
  logWarning (lssEvalMsg [("tag", "derive"), ("ok", true),
    ("derived", Json.arr (derived.map (Json.str ∘ toString))),
    ("via_beq", Json.arr (viaBEq.map (Json.str ∘ toString))),
    ("none", Json.arr (todo.map (Json.str ∘ toString)))])
