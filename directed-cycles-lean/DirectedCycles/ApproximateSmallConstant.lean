import DirectedCycles.ActionBallCardinality

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Below two, the integer covering number is one, so an approximate
subgroup is an actual subgroup. -/
theorem approximate_subgroup_lt_two {G : Type*} [Group G] (A : Set G) (K : ℝ)
    (hA : IsApproximateSubgroup K A) (hK : K < 2) : ∃ H : Subgroup G, (H : Set G) = A := by
  have hone : IsApproximateSubgroup 1 A := by
    refine ⟨hA.one_mem,hA.inv_eq_self,?_⟩
    obtain ⟨F,hF,hcov⟩ := hA.sq_covBySMul
    refine ⟨F,?_,hcov⟩
    have hcard : F.card < 2 := by exact_mod_cast hF.trans_lt hK
    exact_mod_cast (show F.card ≤ 1 by omega)
  exact isApproximateSubgroup_one.mp hone

/-- A positive generating-set power that is a subgroup is the whole group. -/
theorem generating_approximate_power_lt_two {G : Type*} [Group G]
    (S : Set G) (h1 : 1 ∈ S) (hgen : Subgroup.closure S = ⊤)
    (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : K < 2)
    (hA : IsApproximateSubgroup K (S^m)) : S^m = Set.univ := by
  obtain ⟨H,hH⟩ := approximate_subgroup_lt_two (S^m) K hA hK
  have htop : Subgroup.closure (S^m) = ⊤ := by
    rw [Subgroup.closure_pow h1 (by omega),hgen]
  rw [← hH,Subgroup.closure_eq] at htop
  rw [← hH,htop]
  rfl

end DirectedCycles
