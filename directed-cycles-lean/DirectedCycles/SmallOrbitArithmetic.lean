import DirectedCycles.Basic

set_option autoImplicit false
namespace DirectedCycles

/-- A small fibre forces a large orbit quotient, with the exact exponent. -/
theorem small_fibre_quotient_bound (n q m alpha : ℝ) (hn : 0 < n) (hq : 0 < q)
    (hcard : n = q*m) (hm : m < n^alpha) : n^(1-alpha) < q := by
  have hp : 0 < n^alpha := Real.rpow_pos_of_pos hn _
  have hpow : n^(1-alpha)*n^alpha = n := by
    rw [← Real.rpow_add hn,sub_add_cancel,Real.rpow_one]
  have hh : n < q*n^alpha := by
    calc n = q*m := hcard
         _ < q*n^alpha := mul_lt_mul_of_pos_left hm hq
  have hprod : n^(1-alpha)*n^alpha < q*n^alpha := by rw [hpow]; exact hh
  nlinarith

theorem small_quotient_cycle_power (b n q eps lam L : ℝ) (hb : 0 ≤ b) (hn : 0 ≤ n)
    (heps : eps ≤ 1) (hq : n^(1-4*lam) ≤ q) (hL : b*q^(1-eps) ≤ L) :
    b*n^((1-4*lam)*(1-eps)) ≤ L := by
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hn _) hq (by linarith : 0 ≤ 1-eps)
  rw [← Real.rpow_mul hn] at hh
  exact (mul_le_mul_of_nonneg_left hh hb).trans hL

end DirectedCycles
