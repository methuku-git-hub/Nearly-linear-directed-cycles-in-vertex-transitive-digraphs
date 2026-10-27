module

public import DirectedCycles.DyadicCurveLimit

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A quadratic local addition defect tends to zero after dyadic rescaling,
using the norm contraction obtained from the local doubling map. -/
theorem dyadic_curve_addition_bound (f : ℝ → E) {r C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ t : ℝ, |t| ≤ r → ‖f (t/2)‖ ≤ (2/3)*‖f t‖)
    (ha : ∀ s t : ℝ, |s|+|t| ≤ r → ‖f (s+t)-f s-f t‖ ≤ C*(‖f s‖+‖f t‖)^2)
    {s t : ℝ} (hst : |s|+|t| ≤ r) (n : ℕ) :
    ‖dyadicCurve f (s+t) n-dyadicCurve f s n-dyadicCurve f t n‖ ≤
      (C*(‖f s‖+‖f t‖)^2)*(8/9 : ℝ)^n := by
  have hs : |s| ≤ r := by linarith [abs_nonneg t]
  have ht : |t| ≤ r := by linarith [abs_nonneg s]
  have hab : |s/(2 : ℝ)^n|+|t/(2 : ℝ)^n| ≤ r := by
    rw [abs_div,abs_div,abs_of_pos (by positivity : (0 : ℝ)<2^n),← add_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2^n)).2
    have hp : (1 : ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
    have hr : 0 ≤ r := by linarith [abs_nonneg s,abs_nonneg t]
    nlinarith
  have hh := ha (s/(2 : ℝ)^n) (t/(2 : ℝ)^n) hab
  have hnorm : ‖f (s/(2 : ℝ)^n)‖+‖f (t/(2 : ℝ)^n)‖ ≤
      (2/3 : ℝ)^n*(‖f s‖+‖f t‖) := by
    have h1 := dyadic_curve_norm_bound f hc hs n
    have h2 := dyadic_curve_norm_bound f hc ht n
    nlinarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ ‖f (s/(2 : ℝ)^n)‖+‖f (t/(2 : ℝ)^n)‖) hnorm 2
  have he : ‖dyadicCurve f (s+t) n-dyadicCurve f s n-dyadicCurve f t n‖ =
      (2 : ℝ)^n*‖f (s/(2 : ℝ)^n+t/(2 : ℝ)^n)-f (s/(2 : ℝ)^n)-f (t/(2 : ℝ)^n)‖ := by
    dsimp only [dyadicCurve]
    rw [add_div,← smul_sub,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : (0 : ℝ)<2^n)]
  rw [he]
  calc
    _ ≤ (2 : ℝ)^n*(C*(‖f (s/(2 : ℝ)^n)‖+‖f (t/(2 : ℝ)^n)‖)^2) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ (2 : ℝ)^n*(C*((2/3 : ℝ)^n*(‖f s‖+‖f t‖))^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hC) (by positivity)
    _ = (C*(‖f s‖+‖f t‖)^2)*(8/9 : ℝ)^n := by
      have hpow : ((2/3 : ℝ)^n)^2 = ((2/3 : ℝ)^2)^n := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
      have hprod : (2 : ℝ)^n*((2/3 : ℝ)^n)^2 = (8/9 : ℝ)^n := by rw [hpow,← mul_pow]; norm_num
      calc
        _ = (C*(‖f s‖+‖f t‖)^2)*((2 : ℝ)^n*((2/3 : ℝ)^n)^2) := by ring
        _ = _ := by rw [hprod]

/-- The dyadic tangent limits inherit the exact local additive identity from
the vanishing rescaled quadratic defect. -/
theorem dyadic_curve_limit_add (f g : ℝ → E) {r C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ t : ℝ, |t| ≤ r → ‖f (t/2)‖ ≤ (2/3)*‖f t‖)
    (ha : ∀ s t : ℝ, |s|+|t| ≤ r → ‖f (s+t)-f s-f t‖ ≤ C*(‖f s‖+‖f t‖)^2)
    (hlim : ∀ t : ℝ, |t| ≤ r → Filter.Tendsto (dyadicCurve f t) Filter.atTop (𝓝 (g t)))
    {s t : ℝ} (hst : |s|+|t| ≤ r) : g (s+t) = g s+g t := by
  have hs : |s| ≤ r := by linarith [abs_nonneg t]
  have ht : |t| ≤ r := by linarith [abs_nonneg s]
  have hsum : |s+t| ≤ r := (abs_add_le _ _).trans hst
  have hlim' := ((hlim (s+t) hsum).sub (hlim s hs)).sub (hlim t ht)
  have hz : Filter.Tendsto (fun n => dyadicCurve f (s+t) n-dyadicCurve f s n-dyadicCurve f t n)
      Filter.atTop (𝓝 0) := by
    apply squeeze_zero_norm (dyadic_curve_addition_bound f hC hc ha hst)
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 8/9) (by norm_num : (8/9 : ℝ)<1)
    simpa only [mul_zero] using hp.const_mul (C*(‖f s‖+‖f t‖)^2)
  have he := tendsto_nhds_unique hlim' hz
  exact sub_eq_zero.mp (by simpa only [sub_sub] using he)
end DirectedCycles
