module

public import DirectedCycles.DensityPowerArithmetic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- One bounded-prime reconstruction pays the weaker of the small-kernel
and large-kernel constants. -/
noncomputable def budgetConstant (base d M : ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => base
  | t+1 => min (budgetConstant base d M k t/M) (d*(budgetConstant base d M k t)^k)

theorem budgetConstant_pos (base d M : ℝ) (k t : ℕ)
    (hb : 0 < base) (hd : 0 < d) (hM : 0 < M) :
    0 < budgetConstant base d M k t := by
  induction t with
  | zero => exact hb
  | succ t ih => exact lt_min (div_pos ih hM) (mul_pos hd (pow_pos ih k))

theorem budgetConstant_step_le (base d M : ℝ) (k t : ℕ)
    (hb : 0 < base) (hd : 0 < d) (hM : 1 ≤ M) :
    budgetConstant base d M k (t+1) ≤ budgetConstant base d M k t := by
  have hc := budgetConstant_pos base d M k t hb hd (zero_lt_one.trans_le hM)
  exact (min_le_left _ _).trans (div_le_self hc.le hM)

theorem budgetConstant_le_base (base d M : ℝ) (k t : ℕ)
    (hb : 0 < base) (hd : 0 < d) (hM : 1 ≤ M) :
    budgetConstant base d M k t ≤ base := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact (budgetConstant_step_le base d M k t hb hd hM).trans ih

theorem budget_error_step (theta : ℝ) (k t : ℕ) (ht : 0 ≤ theta) (hk : 1 ≤ k) :
    theta ≤ theta*(k : ℝ)^t ∧ theta*(k : ℝ)^t ≤ theta*(k : ℝ)^(t+1) ∧
      theta*(k : ℝ)^(t+1) = (k : ℝ)*(theta*(k : ℝ)^t) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (1 : ℝ) ≤ (k : ℝ)^t := one_le_pow₀ hk1
  constructor
  · exact le_mul_of_one_le_right ht hp
  constructor
  · rw [pow_succ]
    nlinarith [mul_nonneg ht (pow_nonneg (zero_le_one.trans hk1) t)]
  · rw [pow_succ]
    ring

end DirectedCycles
