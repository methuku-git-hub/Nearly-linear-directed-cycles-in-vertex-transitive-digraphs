import DirectedCycles.Basic

set_option autoImplicit false
namespace DirectedCycles

theorem length_bound_iff_density_bound (b N beta L : ℝ) (hN : 0 < N) :
    b*N^(1-beta) ≤ L ↔ b*N^(-beta) ≤ L/N := by
  rw [le_div_iff₀ hN]
  have hpow : N^(1-beta) = N*N^(-beta) := by
    rw [sub_eq_add_neg,Real.rpow_add hN,Real.rpow_one]
  rw [hpow,show b*(N*N^(-beta)) = b*N^(-beta)*N by ring]

theorem density_bound_weaken (b b' beta beta' N L : ℝ)
    (hb : 0 ≤ b) (hbb : b' ≤ b) (he : beta ≤ beta') (hN : 1 ≤ N)
    (hL : b*N^(-beta) ≤ L) : b'*N^(-beta') ≤ L := by
  have hp := Real.rpow_le_rpow_of_exponent_le hN (show -beta' ≤ -beta by linarith)
  exact (mul_le_mul hbb hp (Real.rpow_nonneg (zero_le_one.trans hN) _) hb).trans hL

/-- A bounded kernel loses only its order in cycle density. -/
theorem small_kernel_density (b q K M N beta ell L : ℝ)
    (hb : 0 ≤ b) (hq : 0 < q) (hK : 1 ≤ K) (hKM : K ≤ M)
    (hN : N = q*K) (he : 0 ≤ beta)
    (hell : b*q^(-beta) ≤ ell/q) (hL : ell ≤ L) :
    (b/M)*N^(-beta) ≤ L/N := by
  have hk : 0 < K := zero_lt_one.trans_le hK
  have hm : 0 < M := hk.trans_le hKM
  have hn : 0 < N := hN ▸ mul_pos hq hk
  have hqN : q ≤ N := by rw [hN]; exact le_mul_of_one_le_right hq.le hK
  calc
    b/M*N^(-beta) ≤ b/M*q^(-beta) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hq hqN (by linarith)) (div_nonneg hb hm.le)
    _ ≤ b/K*q^(-beta) := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hb hk hKM) (Real.rpow_nonneg hq.le _)
    _ = (b*q^(-beta))/K := by ring
    _ ≤ (ell/q)/K := div_le_div_of_nonneg_right hell hk.le
    _ = ell/N := by rw [hN]; ring
    _ ≤ L/N := div_le_div_of_nonneg_right hL hn.le

/-- The large-kernel density recurrence multiplies the exponent error by k.
The h-factor is at least one and the B-factor absorbs the lower-class error. -/
theorem large_kernel_density (b d q h B N beta theta ell L : ℝ) (k : ℕ)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hq : 0 < q) (hh : 1 ≤ h) (hB : 1 ≤ B)
    (hN : N = q*h*B) (ht : 0 ≤ theta) (hbeta : theta ≤ (k : ℝ)*beta)
    (hell : b*q^(-beta) ≤ ell/q)
    (hL : d*(ell/q)^k*B^(-theta) ≤ L) :
    d*b^k*N^(-((k : ℝ)*beta)) ≤ L := by
  let gamma : ℝ := k*beta
  have hg : 0 ≤ gamma := ht.trans hbeta
  have hhpos : 0 < h := zero_lt_one.trans_le hh
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hpow : N^(-gamma) ≤ q^(-gamma)*B^(-theta) := by
    rw [hN,Real.mul_rpow (mul_nonneg hq.le hhpos.le) hBpos.le,Real.mul_rpow hq.le hhpos.le]
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hh (neg_nonpos.mpr hg)
    have hbpow := Real.rpow_le_rpow_of_exponent_le hB (show -gamma ≤ -theta by linarith)
    exact mul_le_mul (mul_le_of_le_one_right (Real.rpow_nonneg hq.le _) hp)
      hbpow (Real.rpow_nonneg hBpos.le _) (Real.rpow_nonneg hq.le _)
  have hqpow : q^(-gamma) = (q^(-beta))^k := by
    have hex : -gamma = -beta*(k : ℝ) := by dsimp only [gamma]; ring
    rw [hex,Real.rpow_mul_natCast hq.le]
  have hp : b^k*q^(-gamma) ≤ (ell/q)^k := by
    rw [hqpow,← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hb (Real.rpow_nonneg hq.le _)) hell k
  calc
    d*b^k*N^(-((k : ℝ)*beta)) ≤ d*b^k*(q^(-gamma)*B^(-theta)) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hd (pow_nonneg hb _))
    _ = d*(b^k*q^(-gamma))*B^(-theta) := by ring
    _ ≤ d*(ell/q)^k*B^(-theta) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp hd) (Real.rpow_nonneg hBpos.le _)
    _ ≤ L := hL

end DirectedCycles
