module

public import DirectedCycles.LocalMultiplicationDerivative
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The genuine multiplication chart along a curve has derivative exactly the
chosen continuous linear splitting of its tangent and transverse directions. -/
theorem local_curve_product_hasFDerivAt (μ : E × E → E)
    (hμ : DifferentiableAt ℝ μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id)
    (f : ℝ → E) (hf0 : f 0 = 0) {v : E} (hv : HasDerivAt f v 0)
    (A : (ℝ × F) ≃L[ℝ] E) (hA : ∀ t : ℝ, A (t,0) = t • v) :
    HasFDerivAt (fun p : ℝ × F => μ (f p.1,A (0,p.2))) A.toContinuousLinearMap 0 := by
  let B : (ℝ × F) →L[ℝ] E := A.toContinuousLinearMap.comp
    ((0 : (ℝ × F) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ F))
  have hA0 : A (0,0) = 0 := A.map_zero
  have hfirst : HasFDerivAt (fun p : ℝ × F => f p.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.fst ℝ ℝ F)) 0 := by
    exact hv.hasFDerivAt.comp 0 hasFDerivAt_fst
  have hsecond : HasFDerivAt (fun p : ℝ × F => A (0,p.2)) B 0 := by
    exact A.hasFDerivAt.comp 0 (((0 : (ℝ × F) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ F)).hasFDerivAt)
  have hμd := hμ.hasFDerivAt
  have hμd' : HasFDerivAt μ (fderiv ℝ μ (0,0)) (f (0 : ℝ × F).1,A (0,(0 : ℝ × F).2)) := by
    simpa only [Prod.fst_zero,Prod.snd_zero,hf0,hA0] using hμd
  have hψd := hμd'.comp 0 (hfirst.prodMk hsecond)
  have hD : (fderiv ℝ μ (0,0)).comp
      (((ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.fst ℝ ℝ F)).prod B) = A.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro p
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply]
    rw [fderiv_local_multiplication μ hμ hl hr]
    change (ContinuousLinearMap.toSpanSingleton ℝ v) p.1+A (0,p.2) = A p
    rw [ContinuousLinearMap.toSpanSingleton_apply,← hA p.1,← map_add]
    congr 1
    simp
  rw [hD] at hψd
  exact hψd
end DirectedCycles
