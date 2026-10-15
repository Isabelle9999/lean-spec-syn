-- sent through the lean server as text, appended after the crate text (built the
-- way callgraph.py builds it: import Aeneas + the crate's Code/*.lean files,
-- callees-first) and proof_check.lean, before the per-candidate attempts. not a
-- lake target. proof verdicts come from proof_check.lean's lss_check_proof.
-- needs Aeneas's step infra (`step`, `@[step]`) and Aeneas.Std.WP (spec, dspec,
-- spec_imp_exists, dspec_imp_forall), both already in scope via import Aeneas.
-- no top-level open: this text stays in scope for every later candidate theorem,
-- so an open here would make a crate type named e.g. State or Config ambiguous
-- with Lean's own. each declaration opens only what it needs, scoped to itself.

-- spec m (· = e) -> m = ok e : turns an equation goal into spec form for lss_spec_form.
theorem lss_spec_eq {a} {m : Aeneas.Std.Result a} {e : a}
    (h : Aeneas.Std.WP.spec m (· = e)) : m = Aeneas.Std.Result.ok e := by
  obtain ⟨y, hy, rfl⟩ := Aeneas.Std.WP.spec_imp_exists h
  exact hy

-- m = ok e -> spec m (· = e) : the reverse, for lss_register_step on equation specs.
theorem lss_eq_imp_spec {a} {m : Aeneas.Std.Result a} {e : a}
    (h : m = Aeneas.Std.Result.ok e) : Aeneas.Std.WP.spec m (· = e) :=
  Aeneas.Std.WP.exists_imp_spec ⟨e, h, rfl⟩

-- spec m (fun _ => True) -> ∃ y, m = ok y : the `∃ r, f x = ok r` shape (no `∧ P`),
-- the prompt template's own example.
theorem lss_spec_ex_true {a} {m : Aeneas.Std.Result a}
    (h : Aeneas.Std.WP.spec m (fun _ => True)) : ∃ y, m = Aeneas.Std.Result.ok y := by
  obtain ⟨y, hy, _⟩ := Aeneas.Std.WP.spec_imp_exists h
  exact ⟨y, hy⟩

-- the reverse, for lss_register_step on that shape.
theorem lss_ex_true_imp_spec {a} {m : Aeneas.Std.Result a}
    (h : ∃ y, m = Aeneas.Std.Result.ok y) : Aeneas.Std.WP.spec m (fun _ => True) :=
  Aeneas.Std.WP.exists_imp_spec (h.imp fun _ hy => ⟨hy, trivial⟩)

-- turn a candidate's own goal (∃/equation/∀-then-eq-arrow, under any number of
-- leading ∀ binders) into spec form, so `unfold f; step*` can run on it next.
-- `refine` (not `apply`): apply peels leading pi binders off a lemma's conclusion
-- until something unifies, and dspec_imp_forall's conclusion is itself a pi, so a
-- blind `apply` unifies against any goal by solving its predicate as a constant
-- function — refine does one direct match against the goal, so a mismatched shape
-- just fails and `first` moves on.
macro "lss_spec_form" : tactic =>
  `(tactic| repeat (first
      | refine Aeneas.Std.WP.spec_imp_exists ?_
      | refine lss_spec_eq ?_
      | refine lss_spec_ex_true ?_
      | refine Aeneas.Std.WP.dspec_imp_forall ?_
      | intro _))

-- which converter turns a proved theorem's core (after its leading ∀s) into spec
-- form; none for anything else, in particular the ∀ y, f x = ok y -> P shape, which
-- has no spec-form reverse lemma in WP.lean.
open Lean in
def lssConverterFor (core : Expr) : Option Name :=
  if core.isAppOfArity ``Exists 2 then
    match core.getArg! 1 with
    | .lam _ _ body _ => if body.isAppOfArity ``And 2
                          then some ``Aeneas.Std.WP.exists_imp_spec
                          else some ``lss_ex_true_imp_spec
    | _ => some ``Aeneas.Std.WP.exists_imp_spec
  else if core.isAppOfArity ``Eq 3 then some ``lss_eq_imp_spec
  else none

-- spec m p -> spec m q -> spec m (p ∧ q) : combines two specs proved for the same
-- call, used by lss_register_step to keep one AND-combined @[step] lemma per call
-- instead of letting a weaker later spec silently starve a stronger earlier one.
theorem lss_spec_and {a} {m : Aeneas.Std.Result a} {p q : a → Prop}
    (hp : Aeneas.Std.WP.spec m p) (hq : Aeneas.Std.WP.spec m q) :
    Aeneas.Std.WP.spec m (fun r => p r ∧ q r) := by
  obtain ⟨y, hy, hpy⟩ := Aeneas.Std.WP.spec_imp_exists hp
  obtain ⟨y', hy', hqy⟩ := Aeneas.Std.WP.spec_imp_exists hq
  rw [hy] at hy'
  simp only [Aeneas.Std.Result.ok.injEq] at hy'
  exact Aeneas.Std.WP.exists_imp_spec ⟨y, hy, hpy, hy' ▸ hqy⟩

-- register a proved ∃/equation-shaped theorem's spec-form restatement as a @[step]
-- lemma, so later step* calls (for this theorem's callers, in the same growing env)
-- can use it without unfolding it. skips ∀-arrow-shaped theorems, logging
-- LSS_SKIP_STEP (a warning, since the server drops info messages); any failure in
-- the conversion is caught and logged the same way, since an uncaught error here
-- would otherwise poison the whole (shared, growing) environment.
--
-- keeps one active @[step] lemma per call (the AND of every spec proved for it),
-- since step* tries the newest-registered match first and uses the first one that
-- applies (Tactic/Step/Step.lean:1123-1134) -- so without this, registering a
-- second, weaker spec for a call already covered by a stronger one would starve
-- callers that need the stronger one. `ours` restricts the active-lemma search to
-- lemmas this elaborator itself made (names ending in .step or .comb), so Aeneas's
-- own @[step] lemmas are never touched or replaced.
open Lean Elab Command Meta in
elab "lss_register_step " id:ident : command => do
  let declName := id.getId
  try
    liftTermElabM do
      let ci <- getConstInfo declName
      forallTelescope ci.type fun fvars core => do
        let core <- whnf core
        match lssConverterFor core with
        | none => logWarning m!"LSS_SKIP_STEP {declName}"
        | some conv =>
          let thApp := mkAppN (mkConst declName (ci.levelParams.map mkLevelParam)) fvars
          let proof <- mkAppM conv #[thApp]
          let proofTerm <- mkLambdaFVars fvars proof
          let newTy <- inferType proof
          let thmTy <- mkForallFVars fvars newTy
          let newName := declName ++ `step
          addDecl (.thmDecl (Lean.mkTheoremValEx newName ci.levelParams thmTy proofTerm [newName]))
          -- find the lemma currently active for this call (Init.lean:363), among ours
          let (fExpr, info) <- Aeneas.Step.getStepSpecFunArgsExpr thmTy
          let found <- Aeneas.Step.stepAttr.find? info.spec_name fExpr
          let ours := found.filter (fun n =>
            let s := toString n
            s.endsWith ".step" || s.endsWith ".comb")
          let logStep (action : String) (active : Name) (replaced : Option Name) : MetaM Unit := do
            let fields := #[("call", Lean.Json.str declName.toString),
                            ("action", Lean.Json.str action),
                            ("active", Lean.Json.str active.toString)]
            let fields := match replaced with
              | none => fields
              | some r => fields.push ("replaced", Lean.Json.str r.toString)
            logWarning m!"LSS_STEP {Lean.Json.compress (Lean.Json.mkObj fields.toList)}"
          match ours.back? with
          | none =>
            Lean.Attribute.add newName `step .missing .global
            logStep "new" newName none
          | some oldName =>
            -- same binders: old's constant reapplied to the new lemma's own fvars
            -- must itself typecheck as a fully-applied (non-partial) spec of the
            -- same call -- that fails to elaborate whenever the binder counts or
            -- types differ, or old is a strict prefix (new has fewer binders),
            -- which is exactly "different binders" below.
            let combined? ← try
              let oldCi <- getConstInfo oldName
              let oldApp := mkAppN (mkConst oldName (oldCi.levelParams.map mkLevelParam)) fvars
              let combProof <- mkAppM ``lss_spec_and #[oldApp, proof]
              let combTy <- inferType combProof
              let combProofTerm <- mkLambdaFVars fvars combProof
              let combThmTy <- mkForallFVars fvars combTy
              pure (some (combProofTerm, combThmTy))
            catch _ => pure none
            match combined? with
            | some (combProofTerm, combThmTy) =>
              let combName := declName ++ `comb
              addDecl (.thmDecl (Lean.mkTheoremValEx combName ci.levelParams combThmTy combProofTerm [combName]))
              Lean.Attribute.add combName `step .missing .global
              Lean.Attribute.erase oldName `step
              logStep "combined" combName (some oldName)
            | none =>
              -- different binders: fewer binders stays active (ties keep the old one)
              let oldCi <- getConstInfo oldName
              let oldArity <- forallTelescope oldCi.type fun ys _ => pure ys.size
              if fvars.size < oldArity then
                Lean.Attribute.add newName `step .missing .global
                Lean.Attribute.erase oldName `step
                logStep "kept_new" newName (some oldName)
              else
                logStep "kept_old" oldName none
  catch _ =>
    logWarning m!"LSS_SKIP_STEP {declName}"

-- log every goal still open after step*, one LSS_GOALS warning per goal (a warning,
-- since the server drops info messages). read-only, closes nothing.
open Lean Elab Tactic Meta in
elab "lss_log_goals" : tactic => do
  for g in (<- getGoals) do
    g.withContext do
      let ty <- g.getType
      let head := match ty.getAppFn with
        | .const n _ => toString n
        | _ => "?"
      let text := (<- Lean.Meta.ppExpr ty).pretty
      let json := Lean.Json.mkObj [("head", Lean.Json.str head), ("text", Lean.Json.str text)]
      logWarning m!"LSS_GOALS {Lean.Json.compress json}"
