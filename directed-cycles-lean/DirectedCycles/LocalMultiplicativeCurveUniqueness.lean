module

public import DirectedCycles.AutonomousCurveUniqueness
public import DirectedCycles.LocalCurveDerivativeEquation
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A local multiplicative curve is determined near zero by its identity
tangent. Both derivative equations are derived from the actual local laws. -/
theorem local_multiplicative_curve_eventually_unique (μ : E × E → E)
    (hμ : ContDiffAt ℝ 2 μ (0,0)) (f g : ℝ → E) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    {v : E} (hfv : HasDerivAt f v 0) (hgv : HasDerivAt g v 0)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hfadd : ∀ a b : ℝ, |a|+|b| ≤ r → f (a+b) = μ (f a,f b))
    (hgadd : ∀ a b : ℝ, |a|+|b| ≤ s → g (a+b) = μ (g a,g b)) :
    f =ᶠ[𝓝 (0 : ℝ)] g := by
  let V : E → E := fun x => (fderiv ℝ μ (x,0)) (0,v)
  have hD : ContDiffAt ℝ 1 (fderiv ℝ μ) (0,0) := hμ.fderiv_right (by norm_num)
  have hpair : ContDiffAt ℝ 1 (fun x : E => (x,(0 : E))) 0 := contDiffAt_id.prodMk contDiffAt_const
  have hV : ContDiffAt ℝ 1 V 0 :=
    (hD.comp (f := fun x : E => (x,(0 : E))) 0 hpair).clm_apply (contDiffAt_const (c := (0,v)))
  exact autonomous_curve_eventually_unique V f g (by simpa only [hf0] using hV)
    (hf0.trans hg0.symm)
    (local_curve_derivative_equation μ (hμ.of_le (by norm_num)) f hf0 hfv hr hfadd)
    (local_curve_derivative_equation μ (hμ.of_le (by norm_num)) g hg0 hgv hs hgadd)
end DirectedCycles
