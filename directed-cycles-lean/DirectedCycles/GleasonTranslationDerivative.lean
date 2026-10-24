import DirectedCycles.GleasonLeftDifferenceDerivative
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : GleasonLieAlgebra D ≃L[ℝ] E)

theorem coordinateMul_continuousAt {x y : E}
    (h : coordinateExp D e x*coordinateExp D e y ∈ (coordinateChart D e).target) :
    ContinuousAt (coordinateMul D e) (x,y) := by
  have hc : Continuous (fun p : E × E => coordinateExp D e p.1*coordinateExp D e p.2) :=
    ((continuous_coordinateExp D e).comp continuous_fst).mul ((continuous_coordinateExp D e).comp continuous_snd)
  exact ((coordinateChart D e).symm.continuousAt h).comp_of_eq hc.continuousAt rfl

theorem coordinateMul_left_zero {x : E} (hx : x ∈ (coordinateChart D e).source) :
    coordinateMul D e (x,0) = x := by
  simp only [coordinateMul,coordinateExp_zero,mul_one]
  exact coordinateLog_exp D e hx

theorem coordinateLeftDifference_leftTranslate_eventually {x : E}
    (hx : x ∈ (coordinateChart D e).source) :
    ∀ᶠ y : E in 𝓝 0, coordinateLeftDifference D e x (coordinateMul D e (x,y)) = y := by
  have hxT : coordinateExp D e x ∈ (coordinateChart D e).target := by
    rw [← coordinateChart_coe]
    exact (coordinateChart D e).map_source hx
  have hc : Tendsto (fun y : E => coordinateExp D e x*coordinateExp D e y) (𝓝 0) (𝓝 (coordinateExp D e x)) := by
    have hc0 : Continuous (fun y : E => coordinateExp D e x*coordinateExp D e y) :=
      continuous_const.mul (continuous_coordinateExp D e)
    simpa only [coordinateExp_zero,mul_one] using hc0.tendsto (0 : E)
  have htarget := hc.eventually ((coordinateChart D e).open_target.mem_nhds hxT)
  have hsource : ∀ᶠ y : E in 𝓝 0, y ∈ (coordinateChart D e).source :=
    (coordinateChart D e).open_source.mem_nhds (zero_mem_coordinateChart_source D e)
  filter_upwards [htarget,hsource] with y hyT hyS
  dsimp only [coordinateLeftDifference]
  rw [coordinateExp_mul D e hyT,inv_mul_cancel_left]
  exact coordinateLog_exp D e hyS

variable [FiniteDimensional ℝ E]

/-- The actual local translation has inverse averaged adjoint derivative
at the identity. Its existing topological inverse supplies the inverse
function step, so no differentiable inverse is assumed. -/
theorem coordinateLeftTranslate_hasFDerivAt {x : E}
    (hx : x ∈ (coordinateChart D e).source)
    (hd : HasFDerivAt (coordinateLeftDifference D e x) (coordinateAdjointAverage D e x) x)
    (hu : IsUnit (coordinateAdjointAverage D e x)) :
    HasFDerivAt (fun y : E => coordinateMul D e (x,y))
      (Ring.inverse (coordinateAdjointAverage D e x)) 0 := by
  have hxT : coordinateExp D e x ∈ (coordinateChart D e).target := by
    rw [← coordinateChart_coe]
    exact (coordinateChart D e).map_source hx
  have hc : ContinuousAt (fun y : E => coordinateMul D e (x,y)) 0 :=
    (coordinateMul_continuousAt D e (by simpa only [coordinateExp_zero,mul_one] using hxT)).comp
      (continuous_const.prodMk continuous_id).continuousAt
  obtain ⟨u,hu⟩ := hu
  let U : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit u
  have hU : (U : E →L[ℝ] E) = coordinateAdjointAverage D e x := hu
  have hUi : (U.symm : E →L[ℝ] E) = Ring.inverse (coordinateAdjointAverage D e x) := by
    rw [← hu,Ring.inverse_unit]
    rfl
  have hd' : HasFDerivAt (coordinateLeftDifference D e x) (U : E →L[ℝ] E)
      (coordinateMul D e (x,0)) := by
    rw [hU,coordinateMul_left_zero D e hx]
    exact hd
  have h := HasFDerivAt.of_local_left_inverse hc hd' (coordinateLeftDifference_leftTranslate_eventually D e hx)
  simpa only [hUi] using h

/-- One neighbourhood on which all hypotheses of the derived translation
derivative hold for the actual coordinates. -/
theorem exists_coordinate_translation_derivative_radius : ∃ δ : ℝ, 0 < δ ∧
    ∀ x : E, ‖x‖ < δ → x ∈ (coordinateChart D e).source ∧
      IsUnit (coordinateAdjointAverage D e x) ∧
      HasFDerivAt (coordinateLeftDifference D e x) (coordinateAdjointAverage D e x) x ∧
      HasFDerivAt (fun y : E => coordinateMul D e (x,y))
        (Ring.inverse (coordinateAdjointAverage D e x)) 0 := by
  obtain ⟨r,hr,hd⟩ := coordinateLeftDifference_hasFDerivAt D e
  have hnear : ∀ᶠ x : E in 𝓝 0, x ∈ (coordinateChart D e).source ∧ IsUnit (coordinateAdjointAverage D e x) := by
    filter_upwards [(coordinateChart D e).open_source.mem_nhds (zero_mem_coordinateChart_source D e),
      coordinateAdjointAverage_eventually_isUnit D e] with x hx hu
    exact ⟨hx,hu⟩
  obtain ⟨s,hs,hsB⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨min r s,lt_min hr hs,?_⟩
  intro x hx
  have hxs : x ∈ Metric.ball (0 : E) s := by
    rw [Metric.mem_ball,dist_zero_right]
    exact hx.trans_le (min_le_right _ _)
  obtain ⟨hxS,hxu⟩ := hsB hxs
  have hxd := hd x (hx.trans_le (min_le_left _ _))
  exact ⟨hxS,hxu,hxd,coordinateLeftTranslate_hasFDerivAt D e hxS hxd hxu⟩

end DirectedCycles.GleasonLieAlgebra
