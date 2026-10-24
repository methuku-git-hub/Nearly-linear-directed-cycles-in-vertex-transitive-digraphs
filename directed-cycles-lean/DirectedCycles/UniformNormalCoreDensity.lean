import DirectedCycles.NormalNeighbourhoodDensity
import DirectedCycles.ApproximatePowerCovers

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace FiniteAlmostPeriods

/-- Uniform density for an intersection of at most N short conjugates. -/
theorem uniform_normalCore_density (K τ : ℝ) (hK : 1 ≤ K) (hτ : 0 < τ) (N : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (G : Type*) [Group G] [DecidableEq G]
      (A S X : Finset G), IsApproximateSubgroup K (A : Set G) →
      S ⊆ A^16 → τ*A.card ≤ S.card → S⁻¹ = S →
      1 ∈ X → X ⊆ A^4 → X.card ≤ N →
      ρ*A.card ≤ (normalCoreSet S X).card := by
  classical
  let α := min 1 (τ/K^23)
  let β := α/(K^47)
  have hK0 : 0 < K := by linarith
  have hα : 0 < α := lt_min zero_lt_one (div_pos hτ (by positivity))
  have hα1 : α ≤ 1 := min_le_left _ _
  have hβ : 0 < β := div_pos hα (by positivity)
  have hK47 : 1 ≤ K^47 := one_le_pow₀ hK
  have hβ1 : β ≤ 1 := (div_le_one (by positivity : 0 < K^47)).mpr (hα1.trans hK47)
  refine ⟨β^N,by positivity,?_⟩
  intro G _ _ A S X hA hSA hScard hSi hX1 hXA hXN
  have hAsymm : A⁻¹ = A := by
    apply Finset.coe_injective
    simpa only [Finset.coe_inv] using hA.inv_eq_self
  have hsub : ∀ x ∈ X, conjugateSet S x ⊆ A^24 := by
    intro x hx g hg
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hg
    have hxi : x⁻¹ ∈ A^4 := by
      have hh : x⁻¹ ∈ (A^4)⁻¹ := Finset.inv_mem_inv (hXA hx)
      simpa only [← inv_pow,hAsymm] using hh
    have hh := Finset.mul_mem_mul (Finset.mul_mem_mul (hXA hx) (hSA hs)) hxi
    have he : A^4*A^16*A^4 = A^24 := by rw [← pow_add,← pow_add]
    exact he ▸ hh
  have hU : IsApproximateSubgroup (K^47) ((A^24 : Finset G) : Set G) := by
    simpa only [Finset.coe_pow] using approximate_pow (A : Set G) K hA 24 (by omega)
  have hcard : α*(A^24).card ≤ (S.card : ℝ) := by
    have hp : ((A^24).card : ℝ) ≤ K^23*A.card := by simpa using hA.card_pow_le (n := 24)
    have hατ : α*K^23 ≤ τ := (le_div_iff₀ (by positivity : 0 < K^23)).mp (min_le_right _ _)
    calc
      α*(A^24).card ≤ α*(K^23*A.card) := mul_le_mul_of_nonneg_left hp hα.le
      _ = (α*K^23)*A.card := by ring
      _ ≤ τ*A.card := mul_le_mul_of_nonneg_right hατ (Nat.cast_nonneg _)
      _ ≤ S.card := hScard
  have hc := normalCoreSet_card_lower_bound (A^24) S X (K^47) α hU hα hX1 hSi hsub hcard
  have hpow : β^N ≤ β^X.card := pow_le_pow_of_le_one hβ.le hβ1 hXN
  have hAc : (A.card : ℝ) ≤ (A^24).card := by
    exact_mod_cast Finset.card_le_card (Finset.subset_pow hA.one_mem (by omega : 24 ≠ 0))
  calc
    β^N*A.card ≤ β^X.card*(A^24).card := mul_le_mul hpow hAc (by positivity) (by positivity)
    _ ≤ (normalCoreSet S X).card := hc

end FiniteAlmostPeriods
end DirectedCycles
