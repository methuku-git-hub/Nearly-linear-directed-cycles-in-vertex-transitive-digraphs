import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
open MeasureTheory InnerProductSpace
namespace DirectedCycles
variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [IsProbabilityMeasure μ]

/-- The actual operator obtained by averaging rank-one operators. -/
noncomputable def rankOneAverage (f : X → E) : E →L[ℝ] E :=
  ∫ x, rankOne ℝ (f x) (f x) ∂μ

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [CompleteSpace E] in
/-- Norm continuity of the rank-one integrand follows from continuity
of its vector, even when the original operator action is only strong-continuous. -/
theorem continuous_rankOne_self {f : X → E} (hf : Continuous f) :
    Continuous (fun x => rankOne ℝ (f x) (f x)) :=
  ((rankOne ℝ).continuous.comp hf).clm_apply hf

omit [CompleteSpace E] in
/-- Every rank-one operator is compact, through its actual factorisation
via the one-dimensional scalar space. -/
theorem compact_rankOne (v w : E) : IsCompactOperator (rankOne ℝ v w) := by
  rw [rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℝ v)).comp_clm (innerSL ℝ w)

/-- The average is a compact operator: the compact operators form a
closed real submodule, which contains the Bochner integral. -/
theorem rankOneAverage_compact (f : X → E) (hf : Continuous f) :
    IsCompactOperator (rankOneAverage μ f) := by
  have hi : Integrable (fun x => rankOne ℝ (f x) (f x)) μ :=
    (continuous_rankOne_self hf).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  exact (compactOperator (RingHom.id ℝ) E E).convex.integral_mem
    isClosed_setOfPred_isCompactOperator
    (Filter.Eventually.of_forall (fun x => compact_rankOne (f x) (f x))) hi

omit [CompleteSpace E] in
/-- Evaluation commutes with the actual average. -/
theorem rankOneAverage_apply (f : X → E) (hf : Continuous f) (v : E) :
    rankOneAverage μ f v = ∫ x, inner ℝ (f x) v • f x ∂μ := by
  exact ContinuousLinearMap.integral_apply
    ((continuous_rankOne_self hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) v

/-- The scalar matrix coefficient of the average is its expected
rank-one matrix coefficient. -/
theorem inner_rankOneAverage (f : X → E) (hf : Continuous f) (v w : E) :
    inner ℝ w (rankOneAverage μ f v) =
      ∫ x, inner ℝ (f x) v * inner ℝ w (f x) ∂μ := by
  rw [rankOneAverage_apply μ f hf v]
  have hi : Integrable (fun x => inner ℝ (f x) v • f x) μ :=
    ((hf.inner continuous_const).smul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := ((innerSL ℝ w).integral_comp_comm hi).symm
  change inner ℝ w (∫ x, inner ℝ (f x) v • f x ∂μ) =
    ∫ x, inner ℝ w (inner ℝ (f x) v • f x) ∂μ at h
  simpa only [inner_smul_right,mul_comm] using h

/-- The average is symmetric on the original Hilbert space. -/
theorem rankOneAverage_symmetric (f : X → E) (hf : Continuous f) :
    (rankOneAverage μ f).IsSymmetric := by
  intro v w
  change inner ℝ (rankOneAverage μ f v) w = inner ℝ v (rankOneAverage μ f w)
  rw [real_inner_comm,inner_rankOneAverage μ f hf v w,inner_rankOneAverage μ f hf w v]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [real_inner_comm w (f x),real_inner_comm v (f x),mul_comm])

/-- If the measure has full support, a vector in the kernel of the
average is orthogonal to every vector in the original continuous family. -/
theorem rankOneAverage_kernel_orthogonal [μ.IsOpenPosMeasure]
    (f : X → E) (hf : Continuous f) {v : E} (hv : rankOneAverage μ f v = 0) (x : X) :
    inner ℝ (f x) v = 0 := by
  have he : (∫ y, (inner ℝ (f y) v)^2 ∂μ) = 0 := by
    have h := inner_rankOneAverage μ f hf v v
    rw [hv,inner_zero_right] at h
    convert h.symm using 1
    congr 1
    funext y
    rw [real_inner_comm v (f y),pow_two]
  have hc : Continuous (fun y => (inner ℝ (f y) v)^2) :=
    (hf.inner continuous_const).pow 2
  have ha := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (inner ℝ (f y) v))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp he
  have hall := μ.eq_of_ae_eq ha hc continuous_const
  have hz : (inner ℝ (f x) v)^2 = 0 := congrFun hall x
  nlinarith [sq_nonneg (inner ℝ (f x) v)]
end DirectedCycles
