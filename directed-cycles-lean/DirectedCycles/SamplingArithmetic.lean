module

public import DirectedCycles.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The floor choice and all numerical estimates used in Lemma 4.5. Natural
number division is the floor of the nonnegative rational quotient. -/
theorem sampling_arithmetic (q m d t : ℕ) (hq : 0 < q) (hd : 0 < d)
    (hm : 192 * d * (t + 1) ^ 2 ≤ m) :
    let k := m / (48 * d * (t + 1) ^ 2)
    4 ≤ k ∧ 4 ≤ k * q * d ∧
      ((q * m : ℕ) : ℝ) / (96 * (t + 1 : ℝ) ^ 2) ≤ (k * q * d : ℕ) ∧
      (k : ℝ) * d * (t + 1 : ℝ) ^ 2 / m ≤ 1 / 48 := by
  let b := 48 * d * (t + 1) ^ 2
  let k := m / b
  have hb : 0 < b := by dsimp [b]; positivity
  have h4 : 4 * b ≤ m := by dsimp [b]; nlinarith [hm]
  have hk : 4 ≤ k := (Nat.le_div_iff_mul_le hb).mpr h4
  have hmul : k * b ≤ m := Nat.div_mul_le_self m b
  have hrem : m % b < b := Nat.mod_lt m hb
  have hdiv := Nat.mod_add_div m b
  have hm2 : m ≤ 2 * k * b := by dsimp only [k] at *; nlinarith
  have hmpos : 0 < m := by omega
  have ht : 0 < (t + 1 : ℝ) ^ 2 := by positivity
  have hmpos' : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hmul' : (k : ℝ) * (48 * d * (t + 1 : ℝ) ^ 2) ≤ m := by
    exact_mod_cast hmul
  have hm2' : (m : ℝ) ≤ 2 * k * (48 * d * (t + 1 : ℝ) ^ 2) := by
    exact_mod_cast hm2
  change 4 ≤ k ∧ 4 ≤ k * q * d ∧ _
  refine ⟨hk, hk.trans ((Nat.le_mul_of_pos_right k (by omega : 0 < q)).trans
    (Nat.le_mul_of_pos_right (k * q) hd)), ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 96 * (t + 1 : ℝ) ^ 2)).mpr
    push_cast
    have hq' : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    have h := mul_le_mul_of_nonneg_left hm2' hq'
    nlinarith
  · apply (div_le_iff₀ hmpos').mpr
    nlinarith

end DirectedCycles
