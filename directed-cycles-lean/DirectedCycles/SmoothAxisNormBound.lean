module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth coordinate map vanishing on the first axis and equal to the
identity on the second has a uniform linear bound in its second argument. -/
theorem smooth_axis_norm_bound (f : E × E → E) (hf : ContDiffAt ℝ 2 f (0,0))
    (hleft : ∀ᶠ x : E in 𝓝 0, f (x,0) = 0)
    (hright : (fun y => f (0,y)) =ᶠ[𝓝 (0 : E)] id) :
    ∃ r : ℝ, 0 < r ∧ ∀ x y : E, ‖x‖ < r → ‖y‖ < r → ‖f (x,y)‖ ≤ 2*‖y‖ := by
  let A : E × E → E →L[ℝ] E := fun p => (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ E E)
  have hA : ContDiffAt ℝ 1 A (0,0) :=
    (hf.fderiv_right (by norm_num)).clm_comp contDiffAt_const
  have hA0 : A (0,0) = ContinuousLinearMap.id ℝ E := by
    have hd := (hf.differentiableAt (by norm_num)).hasFDerivAt.comp
      (f := fun y : E => (0,y)) 0 (hasFDerivAt_prodMk_right (0 : E) 0)
    exact hd.unique ((hasFDerivAt_id (𝕜 := ℝ) (0 : E)).congr_of_eventuallyEq hright)
  have hAn : ‖A (0,0)‖ < 2 := by rw [hA0]; linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)]
  have hnorm : ∀ᶠ p : E × E in 𝓝 (0,0), ‖A p‖ < 2 :=
    hA.continuousAt.norm.preimage_mem_nhds (Iio_mem_nhds hAn)
  have hdiff : ∀ᶠ p : E × E in 𝓝 (0,0), DifferentiableAt ℝ f p :=
    (hf.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  have haxis : ∀ᶠ p : E × E in 𝓝 (0,0), f (p.1,0) = 0 :=
    (show Filter.Tendsto (fun p : E × E => p.1) (𝓝 (0,0)) (𝓝 (0 : E)) from continuousAt_fst).eventually hleft
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp ((hdiff.and hnorm).and haxis)
  refine ⟨r,hr,?_⟩
  intro x y hx hy
  have hxy : ∀ z ∈ Metric.closedBall (0 : E) ‖y‖, (x,z) ∈ Metric.ball (0,0) r := by
    intro z hz
    have hzn : ‖z‖ ≤ ‖y‖ := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    simp only [Metric.mem_ball,Prod.dist_eq,dist_zero_right]
    exact max_lt hx (hzn.trans_lt hy)
  have hder : ∀ z ∈ Metric.closedBall (0 : E) ‖y‖,
      HasFDerivWithinAt (fun z => f (x,z)) (A (x,z)) (Metric.closedBall (0 : E) ‖y‖) z := by
    intro z hz
    have hd := (hball (hxy z hz)).1.1.hasFDerivAt.comp
      (f := fun z : E => (x,z)) z (hasFDerivAt_prodMk_right x z)
    exact hd.hasFDerivWithinAt
  have hbound : ∀ z ∈ Metric.closedBall (0 : E) ‖y‖, ‖A (x,z)‖ ≤ 2 :=
    fun z hz => (hball (hxy z hz)).1.2.le
  have hz : (0 : E) ∈ Metric.closedBall 0 ‖y‖ := Metric.mem_closedBall_self (norm_nonneg y)
  have hyB : y ∈ Metric.closedBall (0 : E) ‖y‖ := by simp
  have hh := (convex_closedBall (0 : E) ‖y‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbound hz hyB
  have hzero : f (x,0) = 0 := (hball (hxy 0 hz)).2
  simpa only [hzero,sub_zero] using hh
end DirectedCycles
