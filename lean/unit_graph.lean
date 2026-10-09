-- sent through the lean server as text, appended after the project/source code.
-- not a lake target. callgraph.py appends one final line:
--   #eval LssUnitGraph.dumpUnits (some [`a, `b, ...])   -- explicit names
--   #eval LssUnitGraph.dumpUnits none                   -- every def in the sent text
-- output: one `warning: LSS_UNITS <json>` message (logWarning survives the
-- existing lean_server.check() -> _fmt path; #eval/IO.println info messages do not).

open Lean Lean.Meta

namespace LssUnitGraph

def isRelevantDef (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo _) => true
  | some (.axiomInfo _) => true
  | some (.opaqueInfo _) => true
  | _ => false

def isNoConfusionLike (env : Environment) (n : Name) : Bool :=
  Lean.isNoConfusion env n || (toString n).endsWith "noConfusionType"

-- generic: any binder is instance-implicit, or is a Sort u with u != 0 (a Type-valued binder)
def isGeneric (n : Name) : MetaM Bool := do
  let ci <- getConstInfo n
  forallTelescope ci.type fun xs _ => do
    let mut g := false
    for x in xs do
      let decl <- x.fvarId!.getDecl
      if decl.binderInfo.isInstImplicit then
        g := true
      else
        match decl.type with
        | .sort lvl => if !lvl.isZero then g := true
        | _ => pure ()
    return g

-- use the unfolding equation, not ConstantInfo.value?: compiled recursion
-- (brecOn, WellFounded.fix, ._mutual, Lean.Order.fix) hides callee constants.
def getCallees (n : Name) (keep : List Name) : MetaM (List Name × Bool) := do
  match <- getUnfoldEqnFor? n (nonRec := true) with
  | none => return ([], true)
  | some eqnName =>
    let ci <- getConstInfo eqnName
    let used <- forallTelescope ci.type fun _ body => do
      match body.eq? with
      | some (_, _, rhs) => return rhs.getUsedConstants
      | none => return #[]
    return (used.toList.filter (fun c => keep.contains c), false)

def rangeOf (n : Name) : MetaM (Option (Nat × Nat)) := do
  match <- findDeclarationRanges? n with
  | some dr => return some (dr.range.pos.line, dr.range.endPos.line)
  | none => return none

-- with no explicit list: every definition in the sent text, i.e. added to the
-- env in this elaboration (map₂, not the imported map₁), minus internals,
-- matchers, auxiliary recursors/no-confusion constants, and this file's own
-- helpers (namespaced LssUnitGraph, which share the same elaboration).
def collectNames (namesOpt : Option (List Name)) : MetaM (List Name) := do
  match namesOpt with
  | some ns => return ns
  | none =>
    let env <- getEnv
    let all := env.constants.map₂.toList.map Prod.fst
    let mut result := []
    for n in all do
      if isRelevantDef env n && !(Lean.Name.isInternal n) && !(<- Lean.Meta.isMatcher n)
         && !(Lean.isAuxRecursor env n) && !(isNoConfusionLike env n)
         && !("LssUnitGraph.".isPrefixOf (toString n)) then
        result := n :: result
    return result

def unitJson (n : Name) (allNames : List Name) : MetaM Lean.Json := do
  let (callees, noEqn) <- getCallees n allNames
  let gen <- isGeneric n
  let rng <- rangeOf n
  let rangeJson := match rng with
    | some (st, en) => Lean.Json.arr #[toJson st, toJson en]
    | none => Lean.Json.null
  return Lean.Json.mkObj [
    ("name", toJson (toString n)),
    ("callees", toJson (callees.map toString)),
    ("generic", toJson gen),
    ("range", rangeJson),
    ("no_eqn", toJson noEqn)
  ]

def dumpUnits (namesOpt : Option (List Name)) : MetaM Unit := do
  let names <- collectNames namesOpt
  let units <- names.mapM (fun n => unitJson n names)
  let out := Lean.Json.mkObj [
    ("lean_version", toJson Lean.versionString),
    ("units", Lean.Json.arr units.toArray)
  ]
  logWarning ("LSS_UNITS " ++ (Lean.Json.compress out))

end LssUnitGraph
