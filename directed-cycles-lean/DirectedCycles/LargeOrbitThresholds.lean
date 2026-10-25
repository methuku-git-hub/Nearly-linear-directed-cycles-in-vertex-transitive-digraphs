module

public import DirectedCycles.LogarithmicBounds

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- All quantitative large-orbit inequalities, with a common threshold. -/
theorem large_orbit_thresholds {ell : ℝ} (hell : 0 < ell) (B : ℕ) (hB : 1 ≤ B) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      2 ≤ n ∧ 2 ≤ (n : ℝ) ^ (4 * ell) ∧
      192 * (degreeBudget n B : ℝ) * (connectionSize n ell : ℝ) ^ 2 ≤ (n : ℝ) ^ (4 * ell) ∧
      48 * (connectionSize n ell : ℝ) ^ 2 ≤ (n : ℝ) ^ (3 * ell) := by
  let δ := ell / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let C : ℝ := 16 * (Real.log 2 + 1 / δ) + 4
  let E : ℝ := (B : ℝ) * (1 / (δ * Real.log 2) + 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hBr : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hC : 0 < C := by dsimp [C]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  obtain ⟨N₁, h₁⟩ := eventually_constant_mul_power_le
    (show 0 < 4 * ell by positivity) (show (0 : ℝ) < 2 by norm_num)
  obtain ⟨N₂, h₂⟩ := eventually_constant_mul_power_le
    (show δ + 2 * (ell + δ) < 4 * ell by dsimp [δ]; linarith)
    (show 0 < 192 * E * C ^ 2 by positivity)
  obtain ⟨N₃, h₃⟩ := eventually_constant_mul_power_le
    (show 2 * (ell + δ) < 3 * ell by dsimp [δ]; linarith)
    (show 0 < 48 * C ^ 2 by positivity)
  refine ⟨max 2 (max N₁ (max N₂ N₃)), ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hni : 1 ≤ n := by omega
  have hnx : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₂ : N₂ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hn₃ : N₃ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hc := connectionSize_power_bound n hni hell.le hδ
  change (connectionSize n ell : ℝ) ≤ C * (n : ℝ) ^ (ell + δ) at hc
  have he := degreeBudget_power_bound n B hni hδ
  change (degreeBudget n B : ℝ) ≤ E * (n : ℝ) ^ δ at he
  have hsq : (connectionSize n ell : ℝ) ^ 2 ≤ C ^ 2 * (n : ℝ) ^ (2 * (ell + δ)) := by
    calc (connectionSize n ell : ℝ) ^ 2 ≤ (C * (n : ℝ) ^ (ell + δ)) ^ 2 :=
           pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
         _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hnx.le]; congr 2; ring
  refine ⟨hn2, ?_, ?_, ?_⟩
  · simpa using h₁ n hn₁
  · calc 192 * (degreeBudget n B : ℝ) * (connectionSize n ell : ℝ) ^ 2 ≤
          192 * (E * (n : ℝ) ^ δ) * (C ^ 2 * (n : ℝ) ^ (2 * (ell + δ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) hsq
              (sq_nonneg _) (by positivity)
         _ = (192 * E * C ^ 2) * (n : ℝ) ^ (δ + 2 * (ell + δ)) := by
           rw [Real.rpow_add hnx]; ring
         _ ≤ (n : ℝ) ^ (4 * ell) := h₂ n hn₂
  · exact (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 48)).trans
      (by simpa only [mul_assoc] using h₃ n hn₃)

/-- The numerical conversion from the sampler's denominator to Theorem 3.6. -/
theorem sampling_bound_to_power {n s : ℕ} {ell : ℝ} (hn : 0 < n) (hs : 0 < s)
    (hbound : 48 * (s : ℝ) ^ 2 ≤ (n : ℝ) ^ (3 * ell)) :
    (1 / 2 : ℝ) * (n : ℝ) ^ (1 - 3 * ell) ≤ (n : ℝ) / (96 * (s : ℝ) ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 96 * (s : ℝ) ^ 2)).mpr
  have hm := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hn'.le (1 - 3 * ell))
  have he : (n : ℝ) ^ (1 - 3 * ell) * (n : ℝ) ^ (3 * ell) = (n : ℝ) := by
    rw [← Real.rpow_add hn']; ring_nf; exact Real.rpow_one _
  rw [he] at hm
  nlinarith

end DirectedCycles
