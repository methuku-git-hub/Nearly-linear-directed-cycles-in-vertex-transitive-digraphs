import DirectedCycles.FiniteAlmostPeriods

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace FiniteAlmostPeriods
variable {G : Type*} [Group G]

theorem approximate_pow (A : Set G) (K : ℝ) (hA : IsApproximateSubgroup K A)
    (n : ℕ) (hn : 2 ≤ n) : IsApproximateSubgroup (K^(2*n-1)) (A^n) := by
  have h := hA.pow_inter_pow (IsApproximateSubgroup.subgroup (H := (⊤ : Subgroup G))) hn (by omega : 2 ≤ 2)
  simpa using h

variable [DecidableEq G]

/-- A dense subset of a fixed power gives a uniformly bounded left cover
of another fixed power. The identity is included among the representatives. -/
theorem approximate_power_left_cover (A S : Finset G) (K δ : ℝ)
    (hA : IsApproximateSubgroup K (A : Set G)) (hδ : 0 < δ)
    (hS : S ⊆ A^16) (hcard : δ*A.card ≤ S.card) (hi : S⁻¹ = S) :
    ∃ X : Finset G, 1 ∈ X ∧ X ⊆ A^4 ∧
      X.card ≤ ⌈K^19/δ⌉₊+1 ∧
      (A : Set G)^4 ⊆ (X : Set G)*(S : Set G)^2 := by
  classical
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hA.one_le
  have hAcard : (0 : ℝ) < A.card := by exact_mod_cast (show A.Nonempty from ⟨1,hA.one_mem⟩).card_pos
  have hSnon : S.Nonempty := Finset.card_pos.mp (by
    have hh := (mul_pos hδ hAcard).trans_le hcard
    exact_mod_cast hh)
  have hprod : ((A^4*S).card : ℝ) ≤ (K^19/δ)*S.card := by
    have hsub : A^4*S ⊆ A^20 := by
      calc A^4*S ⊆ A^4*A^16 := Finset.mul_subset_mul (Finset.Subset.refl _) hS
           _ = A^20 := by rw [← pow_add]
    have hc : ((A^4*S).card : ℝ) ≤ (A^20).card := by exact_mod_cast Finset.card_le_card hsub
    have hp : ((A^20).card : ℝ) ≤ K^19*A.card := by simpa using hA.card_pow_le (n := 20)
    have hdiv : (A.card : ℝ) ≤ S.card/δ := (le_div_iff₀ hδ).mpr (by nlinarith [hcard])
    calc
      ((A^4*S).card : ℝ) ≤ K^19*A.card := hc.trans hp
      _ ≤ K^19*(S.card/δ) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = (K^19/δ)*S.card := by ring
  obtain ⟨X,hXA,hXcard,hcover⟩ := Finset.ruzsa_covering_mul hSnon hprod
  refine ⟨insert 1 X,Finset.mem_insert_self _ _,?_,?_,?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.one_mem_pow hA.one_mem
    · exact hXA hx
  · have hX : X.card ≤ ⌈K^19/δ⌉₊ := by exact_mod_cast hXcard.trans (Nat.le_ceil _)
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hX 1)
  · have hs : A^4 ⊆ X*S^2 := by
      simpa only [div_eq_mul_inv,hi,pow_two] using hcover
    have hh : A^4 ⊆ insert 1 X*S^2 := hs.trans
      (Finset.mul_subset_mul (Finset.subset_insert _ _) (Finset.Subset.refl _))
    exact_mod_cast hh

end FiniteAlmostPeriods
end DirectedCycles
