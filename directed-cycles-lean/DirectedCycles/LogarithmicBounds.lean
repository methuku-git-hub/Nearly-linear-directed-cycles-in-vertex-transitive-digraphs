module

public import DirectedCycles.Thresholds

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- An elementary power bound for logarithms, with an explicit constant. -/
theorem log_le_small_power {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) :
    Real.log x ≤ x ^ δ / δ := by
  have hxp : 0 < x := by linarith
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxp δ)
  rw [Real.log_rpow hxp] at h
  apply (le_div_iff₀ hδ).mpr
  nlinarith

theorem log_two_mul_le_small_power {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) :
    Real.log (2 * x) ≤ (Real.log 2 + 1 / δ) * x ^ δ := by
  have hxp : 0 < x := by linarith
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hp : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ.le
  have hl := log_le_small_power hx hδ
  rw [Real.log_mul (by norm_num) hxp.ne']
  have hm := mul_le_mul_of_nonneg_left hp h2
  have he : x ^ δ / δ = (1 / δ) * x ^ δ := by ring
  rw [he] at hl
  nlinarith

theorem ceil_power_le_twice {x ell : ℝ} (hx : 1 ≤ x) (hell : 0 ≤ ell) :
    (⌈x ^ ell⌉₊ : ℝ) ≤ 2 * x ^ ell := by
  have hp := Real.one_le_rpow hx hell
  have hx0 : 0 ≤ x := by linarith
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0 ell)
  linarith

/-- One more than the prescribed connection length, including both ceilings. -/
noncomputable def connectionSize (n : ℕ) (ell : ℝ) : ℕ :=
  2 * ⌈4 * (⌈(n : ℝ) ^ ell⌉₊ : ℝ) * Real.log (2 * (n : ℝ))⌉₊ + 2

/-- A uniform degree budget that also permits the one-orbit loop case. -/
noncomputable def degreeBudget (n B : ℕ) : ℕ :=
  B * (⌈Real.log (n : ℝ) / Real.log 2⌉₊ + 1)

theorem connectionSize_power_bound (n : ℕ) (hn : 1 ≤ n) {ell δ : ℝ}
    (hell : 0 ≤ ell) (hδ : 0 < δ) :
    (connectionSize n ell : ℝ) ≤
      (16 * (Real.log 2 + 1 / δ) + 4) * (n : ℝ) ^ (ell + δ) := by
  have hx : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hxp : 0 < (n : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have hρ := ceil_power_le_twice hx hell
  have hlogbound := log_two_mul_le_small_power hx hδ
  have hρ0 : 0 ≤ (⌈(n : ℝ) ^ ell⌉₊ : ℝ) := Nat.cast_nonneg _
  have hc := Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hρ0) hlog)
  have h1 := mul_le_mul_of_nonneg_right hρ hlog
  have h2 := mul_le_mul_of_nonneg_left hlogbound
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hxp.le ell))
  have hp : 1 ≤ (n : ℝ) ^ (ell + δ) := Real.one_le_rpow hx (by linarith)
  have he : (n : ℝ) ^ ell * (n : ℝ) ^ δ = (n : ℝ) ^ (ell + δ) := (Real.rpow_add hxp ell δ).symm
  dsimp only [connectionSize]
  push_cast
  nlinarith

theorem degreeBudget_power_bound (n B : ℕ) (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    (degreeBudget n B : ℝ) ≤
      (B : ℝ) * (1 / (δ * Real.log 2) + 2) * (n : ℝ) ^ δ := by
  have hx : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hx
  have hc := Nat.ceil_lt_add_one (div_nonneg hlog h2.le)
  have hp : 1 ≤ (n : ℝ) ^ δ := Real.one_le_rpow hx hδ.le
  have hb := div_le_div_of_nonneg_right (log_le_small_power hx hδ) h2.le
  have he : ((n : ℝ) ^ δ / δ) / Real.log 2 = (1 / (δ * Real.log 2)) * (n : ℝ) ^ δ := by ring
  rw [he] at hb
  have hsum : (⌈Real.log (n : ℝ) / Real.log 2⌉₊ : ℝ) + 1 ≤
      (1 / (δ * Real.log 2) + 2) * (n : ℝ) ^ δ := by nlinarith
  have h := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  simpa only [degreeBudget, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using h

theorem eventually_constant_mul_power_le {a b C : ℝ} (hba : b < a) (hC : 0 < C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * (n : ℝ) ^ b ≤ (n : ℝ) ^ a := by
  obtain ⟨N, hN⟩ := eventually_absorb_constant hba (by positivity : 0 < 1 / C)
  refine ⟨N, ?_⟩
  intro n hn
  calc C * (n : ℝ) ^ b ≤ C * ((1 / C) * (n : ℝ) ^ a) :=
         mul_le_mul_of_nonneg_left (hN n hn) hC.le
       _ = (n : ℝ) ^ a := by field_simp

end DirectedCycles
