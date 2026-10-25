module

public import DirectedCycles.OperatorExponentialIntertwining
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

set_option autoImplicit false
open scoped ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The triangular block operator whose exponential contains the averaged
exponential in its upper-right block. -/
noncomputable def exponentialAverageBlock (T : E →L[ℝ] E) : E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.inl ℝ E E).comp
    (T.comp (ContinuousLinearMap.fst ℝ E E)+ContinuousLinearMap.snd ℝ E E)

omit [CompleteSpace E] in
@[simp] theorem exponentialAverageBlock_apply (T : E →L[ℝ] E) (x y : E) :
    exponentialAverageBlock T (x,y) = (T x+y,0) := rfl

/-- An everywhere smooth formula for the operator-valued integral of an
exponential; its definition uses a single convergent block exponential. -/
noncomputable def operatorExponentialAverage (T : E →L[ℝ] E) : E →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E E).comp
    ((NormedSpace.exp (exponentialAverageBlock T)).comp (ContinuousLinearMap.inr ℝ E E))

omit [CompleteSpace E] in
theorem exponentialAverageBlock_contDiff : ContDiff ℝ ∞ (exponentialAverageBlock (E := E)) := by
  exact contDiff_const.clm_comp ((contDiff_id.clm_comp contDiff_const).add contDiff_const)

theorem operatorExponentialAverage_contDiff : ContDiff ℝ ∞ (operatorExponentialAverage (E := E)) := by
  have he : ContDiff ℝ ∞ (NormedSpace.exp : (E × E →L[ℝ] E × E) → (E × E →L[ℝ] E × E)) :=
    (show AnalyticOnNhd ℝ (NormedSpace.exp : (E × E →L[ℝ] E × E) → (E × E →L[ℝ] E × E)) Set.univ
      from fun x _ => NormedSpace.exp_analytic x).contDiff
  exact contDiff_const.clm_comp ((he.comp exponentialAverageBlock_contDiff).clm_comp contDiff_const)

/-- The block formula equals the actual Bochner integral, with no
invertibility assumption on the input operator. -/
theorem operatorExponentialAverage_eq_integral (T : E →L[ℝ] E) :
    operatorExponentialAverage T = ∫ t in (0 : ℝ)..1, NormedSpace.exp (t • T) := by
  let B := exponentialAverageBlock T
  let Q (t : ℝ) : E →L[ℝ] E := (ContinuousLinearMap.fst ℝ E E).comp
    ((NormedSpace.exp (t • B)).comp (ContinuousLinearMap.inr ℝ E E))
  have hQ (t : ℝ) : HasDerivAt Q (NormedSpace.exp (t • T)) t := by
    have h := (hasDerivAt_const t (ContinuousLinearMap.fst ℝ E E)).clm_comp
      ((hasDerivAt_exp_smul_const B t).clm_comp (hasDerivAt_const t (ContinuousLinearMap.inr ℝ E E)))
    have hi := operator_exp_intertwining (t • T) (t • B) (ContinuousLinearMap.inl ℝ E E)
      (by ext v <;> simp [B,exponentialAverageBlock])
    have hd : (ContinuousLinearMap.fst ℝ E E).comp
        ((NormedSpace.exp (t • B)*B).comp (ContinuousLinearMap.inr ℝ E E)) = NormedSpace.exp (t • T) := by
      ext v
      have hv := congrArg (fun L : E →L[ℝ] E × E => (L v).1) hi
      simpa [B,mul_apply_eq_comp] using hv
    simpa only [ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero,zero_add,add_zero,hd] using h
  have hc : Continuous (fun t : ℝ => NormedSpace.exp (t • T)) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_exp_smul_const' T t).continuousAt)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hQ t) (hc.intervalIntegrable 0 1)
  have h0 : Q 0 = 0 := by ext v; simp [Q]
  have h1 : Q 1 = operatorExponentialAverage T := by simp only [Q,one_smul,operatorExponentialAverage,B]
  rw [h0,h1,sub_zero] at hi
  exact hi.symm

@[simp] theorem operatorExponentialAverage_zero : operatorExponentialAverage (0 : E →L[ℝ] E) = 1 := by
  rw [operatorExponentialAverage_eq_integral]
  simp

end DirectedCycles
