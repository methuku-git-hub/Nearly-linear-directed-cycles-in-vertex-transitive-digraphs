import DirectedCycles.Basic

set_option autoImplicit false
namespace DirectedCycles

/-- The logarithmic estimate used in the reachability growth argument. -/
theorem log_growth_lower {ρ : ℝ} (hρ : 1 ≤ ρ) :
    1 / (4 * ρ) ≤ Real.log (1 + 1 / (2 * ρ)) := by
  have hp : 0 < ρ := by linarith
  let x : ℝ := 1 / (2 * ρ)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxu : x ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2 * ρ)).mpr
    linarith
  have hd : 0 < x + 2 := by linarith
  calc 1 / (4 * ρ) = x / 2 := by dsimp [x]; ring
       _ ≤ 2 * x / (x + 2) := by
         apply (le_div_iff₀ hd).mpr
         nlinarith
       _ ≤ Real.log (1 + x) := Real.le_log_one_add_of_nonneg hx

theorem reachability_growth_power {ρ n : ℝ} (hρ : 1 ≤ ρ) (hn : 0 < n)
    (t : ℕ) (ht : 4 * ρ * Real.log (2 * n) ≤ t) :
    2 * n ≤ (1 + 1 / (2 * ρ)) ^ t := by
  have hp : 0 < ρ := by linarith
  have hf : 0 < 1 + 1 / (2 * ρ) := by positivity
  apply (Real.log_le_log_iff (by positivity) (pow_pos hf t)).mp
  rw [Real.log_pow]
  calc Real.log (2 * n) ≤ (t : ℝ) / (4 * ρ) := by
         apply (le_div_iff₀ (by positivity)).mpr
         nlinarith
       _ = (t : ℝ) * (1 / (4 * ρ)) := by ring
       _ ≤ (t : ℝ) * Real.log (1 + 1 / (2 * ρ)) :=
         mul_le_mul_of_nonneg_left (log_growth_lower hρ) (Nat.cast_nonneg _)

theorem reachability_growth_ceil {ρ n : ℝ} (hρ : 1 ≤ ρ) (hn : 0 < n) :
    2 * n ≤ (1 + 1 / (2 * ρ)) ^ ⌈4 * ρ * Real.log (2 * n)⌉₊ :=
  reachability_growth_power hρ hn _ (Nat.le_ceil _)

end DirectedCycles
