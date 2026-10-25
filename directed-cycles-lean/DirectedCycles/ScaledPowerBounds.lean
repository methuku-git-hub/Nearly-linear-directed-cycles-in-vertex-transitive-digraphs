module

public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A uniform integer bound for the quotient obtained by splitting a scaled
power into blocks of length N-1. -/
theorem scaled_floor_div_bound (t : ℝ) (M N : ℕ) (hM : |t| ≤ (M : ℝ)) (hN : 2 ≤ N) :
    -(2*(M : ℤ)) ≤ Int.floor (t*(N : ℝ))/((N : ℤ)-1) ∧
      Int.floor (t*(N : ℝ))/((N : ℤ)-1) ≤ 2*(M : ℤ) := by
  let n := Int.floor (t*(N : ℝ))
  let d : ℤ := (N : ℤ)-1
  let q := n/d
  let r := n%d
  have hN' : (2 : ℤ) ≤ N := by exact_mod_cast hN
  have hd : 0 < d := by dsimp [d]; omega
  have hdN : (N : ℤ) ≤ 2*d := by dsimp [d]; omega
  have hM' : (0 : ℤ) ≤ M := by positivity
  have hbounds : -(M : ℤ)*(N : ℤ) ≤ n ∧ n ≤ (M : ℤ)*(N : ℤ) := by
    have ht := abs_le.mp hM
    constructor
    · apply Int.le_floor.mpr
      push_cast
      exact mul_le_mul_of_nonneg_right ht.1 (by positivity)
    · apply Int.floor_le_iff.mpr
      push_cast
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right ht.2 (by positivity)) (by linarith)
  have hr0 : 0 ≤ r := Int.emod_nonneg n (by omega : d ≠ 0)
  have hrd : r < d := Int.emod_lt_of_pos n hd
  have he : q*d+r = n := by dsimp [q,r]; nlinarith [Int.mul_ediv_add_emod n d]
  have hbound : -(2*(M : ℤ))*d ≤ n ∧ n ≤ (2*(M : ℤ))*d := by
    have hmul := mul_le_mul_of_nonneg_left hdN hM'
    constructor <;> nlinarith [hbounds.1,hbounds.2]
  change -(2*(M : ℤ)) ≤ q ∧ q ≤ 2*(M : ℤ)
  constructor
  · by_contra h
    have hq : q ≤ -(2*(M : ℤ))-1 := by omega
    have hmul := mul_le_mul_of_nonneg_right hq hd.le
    nlinarith [hbound.1]
  · by_contra h
    have hq : 2*(M : ℤ)+1 ≤ q := by omega
    have hmul := mul_le_mul_of_nonneg_right hq hd.le
    nlinarith [hbound.2]
end DirectedCycles
