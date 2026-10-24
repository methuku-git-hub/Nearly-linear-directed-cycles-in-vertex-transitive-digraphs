import DirectedCycles.LocalApproximateGroups
import DirectedCycles.LocalGlobalWordPowers
import Mathlib.Combinatorics.Additive.ApproximateSubgroup

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- The actual local finite cover in a global group is a global approximate
subgroup cover with the same constant. -/
theorem local_global_approximate_conversion {G : Type*} [Group G] {K : ℕ} {A : Finset G}
    (hA : IsLocalFiniteApproximateGroup (LocalGroupAlgebra.ofGroup G) K A) :
    IsApproximateSubgroup (K : ℝ) (A : Set G) := by
  refine ⟨hA.one_mem,?_,?_⟩
  · ext x
    change x⁻¹ ∈ A ↔ x ∈ A
    exact ⟨fun h => by simpa only [LocalGroupAlgebra.ofGroup,inv_inv] using hA.inv_mem _ h,hA.inv_mem x⟩
  · obtain ⟨X,hX,_hi,_hsub,hcover⟩ := hA.cover
    refine ⟨X,by exact_mod_cast hX,?_⟩
    change (A : Set G)^2 ⊆ (X : Set G)*(A : Set G)
    simpa only [LocalGroupAlgebra.ofGroup_wordPower,LocalGroupAlgebra.ofGroup_setMul] using hcover
end DirectedCycles
