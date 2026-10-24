import DirectedCycles.LocalMultiplicationDerivative
import DirectedCycles.DyadicCurveDifferentiable

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Actual local C2 multiplication yields both dyadic contraction and the
quadratic addition estimate on a positive parameter interval. -/
theorem local_multiplicative_curve_estimates (μ : E × E → E)
    (hμ : ContDiffAt ℝ 2 μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id)
    (f : ℝ → E) (hf0 : f 0 = 0) (hfcont : ContinuousAt f 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hmul : ∀ s t : ℝ, |s|+|t| ≤ r₀ → f (s+t) = μ (f s,f t)) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧
      (∀ t : ℝ, |t| ≤ r → ‖f (t/2)‖ ≤ (2/3)*‖f t‖) ∧
      (∀ s t : ℝ, |s|+|t| ≤ r → ‖f (s+t)-f s-f t‖ ≤ K*(‖f s‖+‖f t‖)^2) := by
  have hμ0 : μ (0,0) = 0 := hl.self_of_nhds
  have hdiag := hasFDerivAt_diagonal_twice μ (hμ.differentiableAt (by norm_num)) hl hr
  obtain ⟨a,ha,hexpand⟩ := exists_doubling_expansion (fun x => μ (x,x)) hμ0 hdiag
  obtain ⟨K,b,hK,hb,herror⟩ := local_multiplication_quadratic_error μ hμ hl hr
  have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ‖f t‖ < min a b := by
    have hh := hfcont.norm.preimage_mem_nhds (Iio_mem_nhds (by simpa only [hf0,norm_zero] using lt_min ha hb))
    exact hh
  obtain ⟨δ,hδ,hδf⟩ := Metric.mem_nhds_iff.mp hnear
  let r : ℝ := min r₀ (δ/2)
  have hrpos : 0 < r := lt_min hr₀ (by positivity)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hcontrol : ∀ t : ℝ, |t| ≤ r → ‖f t‖ < min a b := by
    intro t ht
    exact hδf (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht.trans_lt hrδ)
  refine ⟨r,K,hrpos,hK,?_,?_⟩
  · intro t ht
    have ht2 : |t/2| ≤ r := by rw [abs_div]; norm_num; linarith [abs_nonneg t]
    have hh := hexpand (f (t/2)) (lt_of_lt_of_le (hcontrol _ ht2) (min_le_left _ _))
    have he := hmul (t/2) (t/2) (by rw [abs_div]; norm_num; linarith)
    rw [show t/2+t/2=t by ring] at he
    rw [← he] at hh
    linarith
  · intro s t hst
    have hs : |s| ≤ r := by linarith [abs_nonneg t]
    have ht : |t| ≤ r := by linarith [abs_nonneg s]
    rw [hmul s t (hst.trans hrr₀)]
    exact herror (f s) (f t)
      (lt_of_lt_of_le (hcontrol s hs) (min_le_right _ _))
      (lt_of_lt_of_le (hcontrol t ht) (min_le_right _ _))

/-- A continuous local one-parameter curve for a C2 multiplication has a
constructed derivative and a quadratic approximation in its own norm. -/
theorem local_multiplicative_curve_derivative_approximation (μ : E × E → E)
    (hμ : ContDiffAt ℝ 2 μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id)
    (f : ℝ → E) (hf0 : f 0 = 0) (hfcont : ContinuousAt f 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hmul : ∀ s t : ℝ, |s|+|t| ≤ r₀ → f (s+t) = μ (f s,f t)) :
    ∃ v : E, HasDerivAt f v 0 ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ‖f t-t • v‖ ≤ K*‖f t‖^2 := by
  obtain ⟨r,K,hr',hK,hc,ha⟩ := local_multiplicative_curve_estimates μ hμ hl hr f hf0 hfcont hr₀ hmul
  obtain ⟨v,hv⟩ := exists_dyadic_linear_approximation f hf0 hfcont hr' hK hc ha
  have herr : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ‖f t-t • v‖ ≤ (16*K)*‖f t‖^2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr'] with t ht
    have hh : |t| < r := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht
    exact hv t hh.le
  have hK' : 0 ≤ 16*K := by positivity
  exact ⟨v,hasDerivAt_of_curve_quadratic_error f v hf0 hfcont hK' herr,16*K,hK',herr⟩

/-- A continuous local one-parameter curve for a C2 multiplication is
actually differentiable at its identity. -/
theorem local_multiplicative_curve_hasDerivAt (μ : E × E → E)
    (hμ : ContDiffAt ℝ 2 μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id)
    (f : ℝ → E) (hf0 : f 0 = 0) (hfcont : ContinuousAt f 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hmul : ∀ s t : ℝ, |s|+|t| ≤ r₀ → f (s+t) = μ (f s,f t)) :
    ∃ v : E, HasDerivAt f v 0 := by
  obtain ⟨v,hv,_⟩ := local_multiplicative_curve_derivative_approximation μ hμ hl hr f hf0 hfcont hr₀ hmul
  exact ⟨v,hv⟩
end DirectedCycles
