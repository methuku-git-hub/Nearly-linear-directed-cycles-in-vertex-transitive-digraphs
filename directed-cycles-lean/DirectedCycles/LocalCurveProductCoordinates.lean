module

public import DirectedCycles.LocalMultiplicationDerivative
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A smooth local curve with nonzero split tangent supplies actual local
product coordinates by the inverse function theorem. -/
theorem local_curve_product_coordinates (μ : E × E → E)
    (hμ : ContDiffAt ℝ ∞ μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id)
    (f : ℝ → E) (hf0 : f 0 = 0) (hf : ContDiffAt ℝ ∞ f 0)
    {v : E} (hv : HasDerivAt f v 0)
    (A : (ℝ × F) ≃L[ℝ] E) (hA : ∀ t : ℝ, A (t,0) = t • v) :
    ∃ e : OpenPartialHomeomorph (ℝ × F) E,
      (∀ p : ℝ × F, e p = μ (f p.1,A (0,p.2))) ∧
      (0 : ℝ × F) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffAt ℝ ∞ e 0 ∧ ContDiffAt ℝ ∞ e.symm 0 := by
  let ψ : ℝ × F → E := fun p => μ (f p.1,A (0,p.2))
  let B : (ℝ × F) →L[ℝ] E := A.toContinuousLinearMap.comp
    ((0 : (ℝ × F) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ F))
  have hμ0 : μ (0,0) = 0 := hl.self_of_nhds
  have hA0 : A (0,0) = 0 := A.map_zero
  have hψ0 : ψ 0 = 0 := by simp only [ψ,Prod.fst_zero,Prod.snd_zero,hf0,hA0,hμ0]
  have hpairSmooth : ContDiffAt ℝ ∞ (fun p : ℝ × F => (f p.1,A (0,p.2))) 0 :=
    (hf.comp 0 contDiffAt_fst).prodMk (A.contDiff.contDiffAt.comp 0 (contDiffAt_const.prodMk contDiffAt_snd))
  have hψ : ContDiffAt ℝ ∞ ψ 0 := by
    have hh : ContDiffAt ℝ ∞ μ (f (0 : ℝ × F).1,A (0,(0 : ℝ × F).2)) := by
      simpa only [Prod.fst_zero,Prod.snd_zero,hf0,hA0] using hμ
    exact hh.comp 0 hpairSmooth
  have hfirst : HasFDerivAt (fun p : ℝ × F => f p.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.fst ℝ ℝ F)) 0 := by
    exact hv.hasFDerivAt.comp 0 hasFDerivAt_fst
  have hsecond : HasFDerivAt (fun p : ℝ × F => A (0,p.2)) B 0 := by
    exact A.hasFDerivAt.comp 0 (((0 : (ℝ × F) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ F)).hasFDerivAt)
  have hμd := (hμ.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hμd' : HasFDerivAt μ (fderiv ℝ μ (0,0)) (f (0 : ℝ × F).1,A (0,(0 : ℝ × F).2)) := by
    simpa only [Prod.fst_zero,Prod.snd_zero,hf0,hA0] using hμd
  have hψd := hμd'.comp 0 (hfirst.prodMk hsecond)
  have hD : (fderiv ℝ μ (0,0)).comp
      (((ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.fst ℝ ℝ F)).prod B) = A.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro p
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply]
    rw [fderiv_local_multiplication μ (hμ.differentiableAt (by simp)) hl hr]
    change (ContinuousLinearMap.toSpanSingleton ℝ v) p.1+A (0,p.2) = A p
    rw [ContinuousLinearMap.toSpanSingleton_apply,← hA p.1,← map_add]
    congr 1
    simp
  rw [hD] at hψd
  let e := hψ.toOpenPartialHomeomorph ψ hψd (by simp)
  refine ⟨e,fun p => rfl,hψ.mem_toOpenPartialHomeomorph_source hψd (by simp),hψ0,hψ,?_⟩
  have hi := hψ.to_localInverse hψd (by simp)
  simpa only [ContDiffAt.localInverse,ContDiffAt.toOpenPartialHomeomorph,HasStrictFDerivAt.localInverse,e,hψ0] using hi
end DirectedCycles
