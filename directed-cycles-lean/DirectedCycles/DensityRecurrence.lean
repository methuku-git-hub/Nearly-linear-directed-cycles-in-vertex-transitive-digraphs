import DirectedCycles.Basic

set_option autoImplicit false
namespace DirectedCycles

/-- A subgroup-index bound loses at most the first power of the index when
transferring a circumference exponent 1-eta with eta nonnegative. -/
theorem index_power_loss (B C I bound eta : ℝ)
    (hB : B = I*C) (hC : 0 < C) (hI : 1 ≤ I) (hbound : I ≤ bound) (heta : 0 ≤ eta) :
    B^(1-eta) / bound ≤ C^(1-eta) := by
  have hi : 0 < I := lt_of_lt_of_le zero_lt_one hI
  have hb : 0 < bound := hi.trans_le hbound
  apply (div_le_iff₀ hb).mpr
  rw [hB,Real.mul_rpow hi.le hC.le]
  calc
    I^(1-eta)*C^(1-eta) ≤ I*C^(1-eta) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hI (by linarith)) (Real.rpow_nonneg hC.le _)
    _ ≤ C^(1-eta)*bound := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hC.le (1-eta))

/-- The exact density calculation in Theorem 5.1, with the uniform constant
4J and exponent kappa+1. All powers and divisions are justified over positive
quantities; this calculation only requires eta to be nonnegative. -/
theorem directed_lift_density_recurrence (L b T ell h B C I N J eta : ℝ) (kappa : ℕ)
    (hb : 0 < b) (hell : 0 < ell) (hh : 0 < h) (hB : 0 < B) (hC : 0 < C)
    (hN : 0 < N) (hJ : 0 < J) (heta : 0 ≤ eta)
    (hcard : B = I*C) (hI : 1 ≤ I) (hindex : I ≤ J*(N/ell)^kappa)
    (hT : ell*h/4 ≤ T) (hL : b*T*C^(1-eta) ≤ L) :
    b/(4*J)*(ell/N)^(kappa+1)*B^(-eta) ≤ L/(N*h*B) := by
  have hbound : 0 < J*(N/ell)^kappa := mul_pos hJ (pow_pos (div_pos hN hell) _)
  have hpow := index_power_loss B C I (J*(N/ell)^kappa) eta hcard hC hI hindex heta
  have hnonneg : 0 ≤ B^(1-eta)/(J*(N/ell)^kappa) :=
    div_nonneg (Real.rpow_nonneg hB.le _) hbound.le
  have hTnonneg : 0 ≤ T := (div_nonneg (mul_nonneg hell.le hh.le) (by norm_num)).trans hT
  have hlower : b*(ell*h/4)*(B^(1-eta)/(J*(N/ell)^kappa)) ≤ L := by
    refine (show b*(ell*h/4)*(B^(1-eta)/(J*(N/ell)^kappa)) ≤ b*T*C^(1-eta) from ?_).trans hL
    exact mul_le_mul (mul_le_mul_of_nonneg_left hT hb.le) hpow hnonneg (mul_nonneg hb.le hTnonneg)
  have hid : (b*(ell*h/4)*(B^(1-eta)/(J*(N/ell)^kappa)))/(N*h*B) =
      b/(4*J)*(ell/N)^(kappa+1)*B^(-eta) := by
    have hrpow : B^(1-eta) = B*B^(-eta) := by
      rw [sub_eq_add_neg,Real.rpow_add hB,Real.rpow_one]
    rw [hrpow,div_pow,pow_succ,div_pow]
    field_simp
  rw [← hid]
  exact div_le_div_of_nonneg_right hlower (mul_nonneg (mul_nonneg hN.le hh.le) hB.le)

end DirectedCycles
