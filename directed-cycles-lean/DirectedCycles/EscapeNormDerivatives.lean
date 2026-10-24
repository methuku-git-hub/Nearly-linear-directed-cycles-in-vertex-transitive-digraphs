import DirectedCycles.EscapeNormTrapping
import DirectedCycles.FiniteGroupDerivatives

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G] [Fintype G]

theorem abs_pow_sub_one_le (f : G → ℝ) (g : G) (n : ℕ) :
    |f (g^n)-f 1| ≤ (n : ℝ)*derivativeNorm f g := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : |f (g^(n+1))-f (g^n)| ≤ derivativeNorm f g := by
      have h := abs_groupDerivative_le f g (g^(n+1))
      simpa [groupDerivative, leftShift, pow_succ', abs_sub_comm] using h
    calc
      |f (g^(n+1))-f 1| ≤ |f (g^(n+1))-f (g^n)| + |f (g^n)-f 1| := abs_sub_le _ _ _
      _ ≤ derivativeNorm f g + (n : ℝ)*derivativeNorm f g := add_le_add hstep ih
      _ = ((n+1 : ℕ) : ℝ)*derivativeNorm f g := by push_cast; ring

/-- Telescoping gives the escape estimate for any bump supported on the set. -/
theorem escapeNorm_le_derivativeNorm {B : Set G} (hB : 1 ∈ B) (f : G → ℝ)
    (hf1 : 1 ≤ f 1) (hfs : ∀ x, x ∉ B → f x = 0) (g : G) :
    escapeNorm B g ≤ derivativeNorm f g := by
  classical
  by_cases hex : ∃ n : ℕ, g^n ∉ B
  · let n := Nat.find hex
    have hn : g^n ∉ B := Nat.find_spec hex
    have hprev : ∀ i < n, g^i ∈ B := by
      intro i hi
      exact not_not.mp (Nat.find_min hex hi)
    have hn0 : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      exact hn (by simpa [this] using hB)
    rw [escapeNorm_eq_inv_of_first_exit hB hn hprev]
    apply (div_le_iff₀ (by exact_mod_cast hn0 : 0 < (n : ℝ))).2
    have ht := abs_pow_sub_one_le f g n
    rw [hfs _ hn, zero_sub, abs_neg, abs_of_nonneg (by linarith : 0 ≤ f 1)] at ht
    nlinarith
  · have hall : ∀ n : ℕ, g^n ∈ B := by simpa using hex
    rw [(escapeNorm_eq_zero_iff hB g).2 hall]
    exact derivativeNorm_nonneg f g

/-- The BGT trapping/telescoping estimate, with no regularity assumption on the bump. -/
theorem escapeNorm_le_mul_derivativeNorm {A B : Set G} (hB : 1 ∈ B)
    (C : ℕ) (hC : 0 < C)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ B) → x ∈ A)
    (f : G → ℝ) (hf1 : 1 ≤ f 1) (hfs : ∀ x, x ∉ B → f x = 0) (g : G) :
    escapeNorm A g ≤ (C : ℝ)*derivativeNorm f g :=
  (escapeNorm_le_mul_of_trapping hB C hC htrap g).trans
    (mul_le_mul_of_nonneg_left (escapeNorm_le_derivativeNorm hB f hf1 hfs g) (Nat.cast_nonneg C))
end DirectedCycles
