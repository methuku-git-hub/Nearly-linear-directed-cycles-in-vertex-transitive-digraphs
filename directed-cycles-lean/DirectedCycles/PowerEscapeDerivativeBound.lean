module

public import DirectedCycles.EscapeNormDerivatives

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G] [Fintype G]

/-- Taylor's estimate along a power segment whose second derivatives are bounded. -/
theorem derivativeNorm_le_of_power_segment (f : G → ℝ) (g : G) {S : Set G}
    {R : ℝ} (hsecond : ∀ h ∈ S, derivativeNorm (groupDerivative g f) h ≤ R)
    {n : ℕ} (hn : 0 < n) (hp : ∀ i < n, g^i ∈ S) :
    derivativeNorm f g ≤ 2*‖f‖/(n : ℝ)+R := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  apply (derivativeNorm_taylor_bound f g hn).trans
  have hsum : (∑ i ∈ Finset.range n, derivativeNorm (groupDerivative g f) (g^i)) ≤ (n : ℝ)*R := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n, R := by
        apply Finset.sum_le_sum
        intro i hi
        exact hsecond _ (hp i (Finset.mem_range.mp hi))
      _ = (n : ℝ)*R := by simp
  calc
    (2*‖f‖ + ∑ i ∈ Finset.range n, derivativeNorm (groupDerivative g f) (g^i))/(n : ℝ) ≤
        (2*‖f‖+(n : ℝ)*R)/(n : ℝ) :=
      div_le_div_of_nonneg_right (add_le_add le_rfl hsum) hnR.le
    _ = 2*‖f‖/(n : ℝ)+R := by field_simp

/-- The power length can be eliminated in favour of the actual escape norm.
This includes zero escape norm, rather than assuming a finite first exit. -/
theorem derivativeNorm_le_escape_of_second (f : G → ℝ) (g : G) {S : Set G}
    (hS : 1 ∈ S) {R : ℝ} (hR : 0 ≤ R)
    (hsecond : ∀ h ∈ S, derivativeNorm (groupDerivative g f) h ≤ R) :
    derivativeNorm f g ≤ 4*‖f‖*escapeNorm S g + R := by
  classical
  by_cases hex : ∃ n : ℕ, g^n ∉ S
  · let n := Nat.find hex
    have hn : g^n ∉ S := Nat.find_spec hex
    have hp : ∀ i < n, g^i ∈ S := fun i hi => not_not.mp (Nat.find_min hex hi)
    have hn0 : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      exact hn (by simpa [this] using hS)
    rw [escapeNorm_eq_inv_of_first_exit hS hn hp]
    by_cases hn1 : n = 1
    · simp only [hn1, Nat.cast_one, div_one, mul_one]
      have h := derivativeNorm_le_two_mul f g
      have := norm_nonneg f
      linarith
    · have hn2 : 2 ≤ n := by omega
      have hm0 : 0 < n-1 := by omega
      have hnr : 0 < (n : ℝ) := by exact_mod_cast hn0
      have hmr : 0 < ((n-1 : ℕ) : ℝ) := by exact_mod_cast hm0
      have hnm : (n : ℝ) ≤ 2*((n-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ 2*(n-1))
      apply (derivativeNorm_le_of_power_segment f g hsecond hm0
        (fun i hi => hp i (by omega))).trans
      apply add_le_add _ le_rfl
      rw [mul_one_div]
      apply (div_le_div_iff₀ hmr hnr).2
      have := norm_nonneg f
      nlinarith
  · have hall : ∀ n : ℕ, g^n ∈ S := by simpa using hex
    rw [(escapeNorm_eq_zero_iff hS g).2 hall, mul_zero, zero_add]
    by_contra h
    have hδ : 0 < derivativeNorm f g - R := by linarith
    obtain ⟨n,hn⟩ := exists_nat_gt (2*‖f‖/(derivativeNorm f g-R))
    have hn0r : 0 < (n : ℝ) := (div_nonneg (by positivity) hδ.le).trans_lt hn
    have hn0 : 0 < n := by exact_mod_cast hn0r
    have ht := derivativeNorm_le_of_power_segment f g hsecond hn0 (fun i _ => hall i)
    have hprod := (div_lt_iff₀ hδ).mp hn
    have hprod' : (derivativeNorm f g-R)*(n : ℝ) ≤ 2*‖f‖ :=
      (le_div_iff₀ hn0r).mp (by linarith : derivativeNorm f g-R ≤ 2*‖f‖/(n : ℝ))
    nlinarith
end DirectedCycles
