import DirectedCycles.FiniteSmallNeighbourhoods
import DirectedCycles.EscapeSublevelPowers

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- A bounded power-trapping condition upgrades the proved finite root-set
theorem to approximate groups whose prescribed powers have arbitrarily small
escape norm. Both density and covering bounds are uniform in the finite group. -/
theorem finite_escape_neighbourhoods (K : ℝ) (hK : 1 ≤ K) (C m : ℕ)
    (r : ℝ) (hr : 0 < r) :
    ∃ L d : ℝ, 1 ≤ L ∧ 0 < d ∧
      ∀ (G : Type*) [Group G] [DecidableEq G] (A : Finset G),
      IsApproximateSubgroup K (A : Set G) →
      (∀ x : G, (∀ k : ℕ, 1 ≤ k → k ≤ C → x^k ∈ (A : Set G)^4) → x ∈ A) →
      ∃ B : Finset G, IsApproximateSubgroup L (B : Set G) ∧
        d*A.card ≤ B.card ∧ (B : Set G)^m ⊆ escapeSublevel A r := by
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hr
  obtain ⟨L,d,hL,hd,hsmall⟩ := FiniteAlmostPeriods.finite_small_neighbourhoods K hK (m*(N*C))
  refine ⟨L,d,hL,hd,?_⟩
  intro G _ _ A hA htrap
  obtain ⟨B,hB,hBd,hBpow⟩ := hsmall G A hA
  refine ⟨B,hB,hBd,?_⟩
  intro x hx
  have hp : ∀ j ≤ N, x^j ∈ (A : Set G) := by
    intro j hj
    apply htrap (x^j)
    intro k _ hk
    have hmem : (x^j)^k ∈ (B : Set G)^(m*(j*k)) := by
      rw [pow_mul (B : Set G) m (j*k)]
      simpa only [← pow_mul] using Set.pow_mem_pow (n := j*k) hx
    have hle : m*(j*k) ≤ m*(N*C) := Nat.mul_le_mul_left m (Nat.mul_le_mul hj hk)
    exact hBpow (Set.pow_subset_pow_right hB.one_mem hle hmem)
  exact (escapeNorm_le_of_powers hp).trans hN.le
end DirectedCycles
