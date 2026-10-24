import DirectedCycles
import Lean.Util.CollectAxioms
open Lean Elab Term Meta
set_option maxHeartbeats 0 in
run_elab do
  let env ← getEnv
  let name := `DirectedCycles.theorem_1_5
  let some (.thmInfo ci) := env.find? name | throwError "Missing main theorem"
  let same ← isDefEq ci.type (mkConst `DirectedCycles.MainTheorem)
  unless same do throwError "Wrong main theorem type"
  let axioms ← collectAxioms name
  logInfo m!"MAIN_JSON {Json.mkObj [("theorem_present",toJson true),("exact_target_type",toJson same),("axioms",toJson (axioms.map Name.toString))] |>.compress}"
namespace Verification

/-- Dependencies of types, bodies, and inductive/recursor metadata. -/
def dependencies (ci : ConstantInfo) : Array Name := Id.run do
  let mut ds := ci.type.getUsedConstants
  if let some value := ci.value? (allowOpaque := true) then
    ds := ds ++ value.getUsedConstants
  match ci with
  | .inductInfo v => ds := ds ++ v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => ds := ds.push v.induct
  | .recInfo v =>
    ds := ds ++ v.all.toArray
    for rule in v.rules do
      ds := (ds.push rule.ctor) ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return ds.toList.eraseDups.toArray.qsort Name.lt

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient_primitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

end Verification

set_option maxHeartbeats 0 in
run_elab do
  let env ← getEnv
  let root := `DirectedCycles.theorem_1_5
  let mut pending := #[root]
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  let mut axioms : Array String := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := env.checked.get.find? name | throwError "Missing closure constant {name}"
    if ci.isUnsafe then throwError "Unsafe constant in main closure: {name}"
    let deps := Verification.dependencies ci
    pending := pending ++ deps
    let modName := match env.getModuleIdxFor? name with
      | some i => (env.header.moduleNames[i.toNat]?.getD .anonymous).toString
      | none => "[current audit]"
    if let .axiomInfo _ := ci then axioms := axioms.push name.toString
    rows := rows.push (Json.mkObj [
      ("name", toJson name.toString),
      ("kind", toJson (Verification.kind ci)),
      ("module", toJson modName),
      ("dependencies", toJson (deps.map Name.toString))])
  let row := Json.mkObj [
    ("root", toJson root.toString),
    ("scope", toJson "Transitive kernel constants in types, proof/definition bodies, inductive declarations, constructors and recursor rules. Inductive metadata may create cycles."),
    ("complete", toJson true),
    ("axioms", toJson (axioms.qsort (· < ·))),
    ("declarations", toJson rows)]
  IO.FS.writeFile "verification/main-constant-closure.json" (row.compress ++ "\n")
  logInfo m!"CLOSURE_JSON {Json.mkObj [("count",toJson rows.size),("complete",toJson true),("axioms",toJson axioms)] |>.compress}"

-- Independently spell out the requested quantifiers, graph hypotheses and bound.
example : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ D : DirectedCycles.Digraph (Fin n), DirectedCycles.Loopless D →
      DirectedCycles.Connected D → DirectedCycles.VertexTransitive D →
        ∃ C : DirectedCycles.Cycle D, (n : ℝ) ^ (1 - ε) ≤ (C.length : ℝ) :=
  DirectedCycles.theorem_1_5
