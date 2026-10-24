import DirectedCycles.LocalMultiplicativeCurveDerivative
import DirectedCycles.LocalCurveDerivativeEquation
import DirectedCycles.AutonomousCurveSmoothness

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuous one-parameter curve for an actual smooth local multiplication
is smooth at the identity. The proof constructs its derivative by dyadic limits
and then bootstraps the transported derivative equation. -/
theorem local_multiplicative_curve_contDiffAt (μ : E × E → E)
    (hμ : ContDiffAt ℝ ∞ μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id)
    (f : ℝ → E) (hf0 : f 0 = 0) (hfcont : ContinuousAt f 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hmul : ∀ s t : ℝ, |s|+|t| ≤ r₀ → f (s+t) = μ (f s,f t)) :
    ContDiffAt ℝ ∞ f 0 := by
  obtain ⟨v,hv⟩ := local_multiplicative_curve_hasDerivAt μ (hμ.of_le (by simp)) hl hr f hf0 hfcont hr₀ hmul
  let V : E → E := fun x => (fderiv ℝ μ (x,0)) (0,v)
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ μ) (0,0) := hμ.fderiv_right (by simp)
  have hpair : ContDiffAt ℝ ∞ (fun x : E => (x,(0 : E))) 0 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hV : ContDiffAt ℝ ∞ V 0 :=
    (hD.comp (f := fun x : E => (x,(0 : E))) 0 hpair).clm_apply (contDiffAt_const (c := (0,v)))
  exact contDiffAt_of_autonomous_derivative f V (by simpa only [hf0] using hV)
    (local_curve_derivative_equation μ (hμ.of_le (by simp)) f hf0 hv hr₀ hmul)
end DirectedCycles
