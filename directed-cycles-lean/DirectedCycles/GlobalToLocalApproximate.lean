module

public import DirectedCycles.LocalApproximateGroups
public import DirectedCycles.LocalGlobalWordPowers
public import DirectedCycles.SymmetricApproximateCover

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- The library's global approximate-group convention supplies the precise
finite local definition, with a proved factor-two conversion of the cover. -/
theorem global_to_local_approximate {K : ℕ} {A : Finset G} (hK : 1 ≤ K)
    (hA : IsApproximateSubgroup (K : ℝ) (A : Set G)) :
    IsLocalFiniteApproximateGroup (LocalGroupAlgebra.ofGroup G) (2*K) A := by
  refine ⟨by omega,hA.one_mem,?_,LocalGroupAlgebra.ofGroup_allProductsDefined _ _,?_⟩
  · intro x hx
    change x⁻¹ ∈ (A : Set G)
    have hh : x⁻¹ ∈ (A : Set G)⁻¹ := Set.inv_mem_inv.mpr hx
    simpa only [hA.inv_eq_self] using hh
  · obtain ⟨X,hcard,hi,hsub,hcov⟩ := symmetric_approximate_cover hA
    refine ⟨X,hcard,hi,?_,?_⟩
    · simpa only [LocalGroupAlgebra.ofGroup_wordPower] using hsub
    · simpa only [LocalGroupAlgebra.ofGroup_wordPower,LocalGroupAlgebra.ofGroup_setMul] using hcov
end DirectedCycles
