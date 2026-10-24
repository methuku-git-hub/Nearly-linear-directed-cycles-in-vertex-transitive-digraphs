import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Topology.Algebra.OpenSubgroup

set_option autoImplicit false
open scoped Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ,E) ∞ G]

/-- The ordinary open-submanifold charts on an open subgroup. -/
@[instance_reducible]
noncomputable def openSubgroupChartedSpace (S : Subgroup G) (hS : IsOpen (S : Set G)) :
    ChartedSpace E S :=
  inferInstanceAs (ChartedSpace E (⟨(S : Set G),hS⟩ : TopologicalSpace.Opens G))

/-- An open subgroup inherits the actual smooth multiplication and inverse
by its open-submanifold charts, without a Lie existence assumption. -/
theorem open_subgroup_lie_group (S : Subgroup G) (hS : IsOpen (S : Set G)) :
    let := openSubgroupChartedSpace (E := E) S hS
    LieGroup 𝓘(ℝ,E) ∞ S := by
  let U : TopologicalSpace.Opens G := ⟨(S : Set G),hS⟩
  let : Group U := inferInstanceAs (Group S)
  let := openSubgroupChartedSpace (E := E) S hS
  have hval : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (S.subtype : S → G) :=
    contMDiff_subtype_val (U := U)
  have hmul : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
      (fun p : S × S => (p.1.val*p.2.val : G)) :=
    (hval.comp contMDiff_fst).mul (hval.comp contMDiff_snd)
  have hinv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x : S => (x.val : G)⁻¹) := hval.inv
  exact { toIsManifold := IsManifold.mk' 𝓘(ℝ,E) ∞ U
          contMDiff_mul := (ContMDiff.subtypeVal_comp_iff U (fun p : S × S => p.1*p.2)).1 hmul
          contMDiff_inv := (ContMDiff.subtypeVal_comp_iff U (fun x : S => x⁻¹)).1 hinv }
end DirectedCycles
