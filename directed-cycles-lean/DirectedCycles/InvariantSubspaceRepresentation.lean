module

public import DirectedCycles.NormedRingUnitsNSS
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : G →* E →L[ℝ] E) (S : Submodule ℝ E)
    (hS : ∀ g v, v ∈ S → R g v ∈ S)

/-- The actual representation restricted to an invariant subspace. -/
def invariantSubspaceRepresentation : G →* S →L[ℝ] S where
  toFun g := (R g).restrict (hS g)
  map_one' := by ext v; exact congrArg (fun A : E →L[ℝ] E => A v) (map_one R)
  map_mul' g h := by
    ext v
    exact congrArg (fun A : E →L[ℝ] E => A v) (map_mul R g h)

omit [IsTopologicalGroup G] in
/-- In finite dimension, strong continuity of the original action gives
operator-norm continuity of the restriction. -/
theorem invariantSubspaceRepresentation_continuous [FiniteDimensional ℝ S]
    (hc : ∀ v, Continuous (fun g => R g v)) :
    Continuous (invariantSubspaceRepresentation R S hS) := by
  apply continuous_clm_apply.mpr
  intro v
  exact (hc (v : E)).subtype_mk _

/-- Group inverses turn the restriction into an actual unit-valued homomorphism. -/
def invariantSubspaceUnitsRepresentation : G →* (S →L[ℝ] S)ˣ :=
  (invariantSubspaceRepresentation R S hS).toHomUnits

/-- Both the operator and its inverse vary continuously. -/
theorem invariantSubspaceUnitsRepresentation_continuous [FiniteDimensional ℝ S]
    (hc : ∀ v, Continuous (fun g => R g v)) :
    Continuous (invariantSubspaceUnitsRepresentation R S hS) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact invariantSubspaceRepresentation_continuous R S hS hc
  · exact (invariantSubspaceRepresentation_continuous R S hS hc).comp continuous_inv

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A moved vector in the subspace proves that the unit-valued
restriction separates the given group element from the identity. -/
theorem invariantSubspaceUnitsRepresentation_ne_one {g : G} {v : E}
    (hv : v ∈ S) (hne : R g v ≠ v) : invariantSubspaceUnitsRepresentation R S hS g ≠ 1 := by
  intro he
  have h := congrArg (fun u : (S →L[ℝ] S)ˣ => ((u : S →L[ℝ] S) ⟨v,hv⟩ : E)) he
  exact hne h
end DirectedCycles
