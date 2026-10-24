import DirectedCycles.Basic

set_option autoImplicit false

namespace DirectedCycles

/-- A strict exponent margin absorbs any positive multiplicative constant. -/
theorem eventually_absorb_constant {a b c : ℝ} (hba : b < a) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n : ℝ) ^ b ≤ c * (n : ℝ) ^ a := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 / c) ^ (1 / (a - b)))
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hab : 0 < a - b := sub_pos.mpr hba
  have hbase : (1 / c) ^ (1 / (a - b)) ≤ (n : ℝ) :=
    hN.le.trans (by exact_mod_cast hnN)
  have hp : 1 / c ≤ (n : ℝ) ^ (a - b) := by
    calc
      1 / c = ((1 / c) ^ (1 / (a - b))) ^ (a - b) := by
        rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hab.ne', Real.rpow_one]
      _ ≤ (n : ℝ) ^ (a - b) := Real.rpow_le_rpow (by positivity) hbase hab.le
  have hone : 1 ≤ c * (n : ℝ) ^ (a - b) := by
    have := (div_le_iff₀ hc).mp hp
    nlinarith
  calc
    (n : ℝ) ^ b = 1 * (n : ℝ) ^ b := by ring
    _ ≤ (c * (n : ℝ) ^ (a - b)) * (n : ℝ) ^ b :=
      mul_le_mul_of_nonneg_right hone (Real.rpow_nonneg hnpos.le _)
    _ = c * (n : ℝ) ^ a := by
      rw [mul_assoc, ← Real.rpow_add hnpos, sub_add_cancel]

theorem main_exponent_margins {ε : ℝ} (hε : 0 < ε) :
    1 - ε < 1 - 3 * (ε / 10) ∧
    1 - ε < (1 - 4 * (ε / 10)) * (1 - ε / 3) := by
  constructor
  · linarith
  · nlinarith [sq_nonneg ε]

/-- Both numerical thresholds in the final paragraph of the main proof.
This proves only numerical absorption, not either graph-theoretic bound. -/
theorem main_thresholds {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ (1 - ε) ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (1 - 3 * (ε / 10)) ∧
      (n : ℝ) ^ (1 - ε) ≤ c * (n : ℝ) ^ ((1 - 4 * (ε / 10)) * (1 - ε / 3)) := by
  obtain ⟨N₁, h₁⟩ := eventually_absorb_constant (main_exponent_margins hε).1
    (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨N₂, h₂⟩ := eventually_absorb_constant (main_exponent_margins hε).2 hc
  exact ⟨max N₁ N₂, fun n hn =>
    ⟨h₁ n ((le_max_left _ _).trans hn), h₂ n ((le_max_right _ _).trans hn)⟩⟩

end DirectedCycles
