module

public import DirectedCycles.LocalMultiplicationDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Comp

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiating genuine local associativity makes the coordinate vector
field left invariant. All derivatives occur inside the actual local domain. -/
theorem local_multiplication_invariant_field (μ : E × E → E)
    (hμ : ContDiffAt ℝ 1 μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hassoc : ∀ᶠ p : E × E in 𝓝 (0,0),
      (fun z => μ (μ (p.1,p.2),z)) =ᶠ[𝓝 (0 : E)] (fun z => μ (p.1,μ (p.2,z)))) (v : E) :
    ∀ᶠ p : E × E in 𝓝 (0,0),
      (fderiv ℝ μ (p.1,p.2)) (0,(fderiv ℝ μ (p.2,0)) (0,v)) =
        (fderiv ℝ μ (μ (p.1,p.2),0)) (0,v) := by
  have h0 : μ (0,0) = 0 := hl.self_of_nhds
  have hdiff : ∀ᶠ p : E × E in 𝓝 (0,0), DifferentiableAt ℝ μ p :=
    (hμ.eventually (by simp)).mono (fun p hp => hp.differentiableAt one_ne_zero)
  have hc : ContinuousAt (fun p : E × E => (μ p,(0 : E))) (0,0) :=
    hμ.continuousAt.prodMk continuousAt_const
  have hout : ∀ᶠ p : E × E in 𝓝 (0,0), DifferentiableAt ℝ μ (μ p,0) :=
    (show Filter.Tendsto (fun p : E × E => (μ p,(0 : E))) (𝓝 (0,0)) (𝓝 (0,0)) by
      simpa only [h0] using hc.tendsto).eventually hdiff
  have hy : ∀ᶠ p : E × E in 𝓝 (0,0), DifferentiableAt ℝ μ (p.2,0) :=
    (continuousAt_snd.prodMk continuousAt_const).eventually hdiff
  have hSnd : Filter.Tendsto (fun p : E × E => p.2) (𝓝 ((0 : E),0)) (𝓝 0) := continuousAt_snd
  have hly : ∀ᶠ p : E × E in 𝓝 (0,0), μ (p.2,0) = p.2 := hSnd.eventually hl
  filter_upwards [hassoc,hdiff,hout,hy,hly] with p ha hp ho hy hly
  have hlD : HasFDerivAt (fun z : E => μ (μ p,z))
      ((fderiv ℝ μ (μ p,0)).comp (ContinuousLinearMap.inr ℝ E E)) 0 :=
    ho.hasFDerivAt.comp (f := fun z : E => (μ p,z)) 0 (hasFDerivAt_prodMk_right (μ p) 0)
  have hiD : HasFDerivAt (fun z : E => μ (p.2,z))
      ((fderiv ℝ μ (p.2,0)).comp (ContinuousLinearMap.inr ℝ E E)) 0 :=
    hy.hasFDerivAt.comp (f := fun z : E => (p.2,z)) 0 (hasFDerivAt_prodMk_right p.2 0)
  have hp' : HasFDerivAt μ (fderiv ℝ μ p) (p.1,μ (p.2,0)) := by
    simpa only [hly] using hp.hasFDerivAt
  have hrD := hp'.comp (f := fun z : E => (p.1,μ (p.2,z))) 0
    ((hasFDerivAt_const p.1 0).prodMk hiD)
  have he := (hlD.congr_of_eventuallyEq ha.symm).unique hrD
  have hev := congrArg (fun D : E →L[ℝ] E => D v) he
  change (fderiv ℝ μ (μ p,0)) (0,v) =
    (fderiv ℝ μ p) (0,(fderiv ℝ μ (p.2,0)) (0,v)) at hev
  exact hev.symm
end DirectedCycles
