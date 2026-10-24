import DirectedCycles.GleasonSmoothMultiplication
import DirectedCycles.GleasonDifferenceChart

set_option autoImplicit false
open Filter Topology
open scoped Topology ContDiff
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- Smooth multiplication gives smooth left-difference charts at all
small base points, by the actual inverse chart and its proved derivative. -/
theorem exists_coordinate_smooth_difference_radius : ∃ δ : ℝ, 0 < δ ∧
    ∀ x : E, ‖x‖ < δ → x ∈ (coordinateChart D e).source ∧
      ContDiffAt ℝ ∞ (coordinateLeftDifference D e x) x ∧
      ContDiffAt ℝ ∞ (fun y : E => coordinateMul D e (x,y)) 0 := by
  obtain ⟨r,hr,hμ⟩ := coordinateMul_contDiff_near_zero D e
  obtain ⟨s,hs,hdata⟩ := exists_coordinate_translation_derivative_radius D e
  refine ⟨min r s,lt_min hr hs,?_⟩
  intro x hx
  obtain ⟨hxS,hxu,_hxd,hxt⟩ := hdata x (hx.trans_le (min_le_right _ _))
  have hxB : (x,0) ∈ Metric.ball (0 : E × E) r := by
    rw [Metric.mem_ball,dist_zero_right,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg x)]
    exact hx.trans_le (min_le_left _ _)
  have hμx : ContDiffAt ℝ ∞ (coordinateMul D e) (x,0) :=
    hμ.contDiffAt (Metric.isOpen_ball.mem_nhds hxB)
  have htx : ContDiffAt ℝ ∞ (fun y : E => coordinateMul D e (x,y)) 0 :=
    hμx.comp (0 : E) (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨hxS,?_,htx⟩
  let f := (coordinateDifferenceChart D e x).symm
  have hf : (f : E → E) = (fun y : E => coordinateMul D e (x,y)) :=
    funext (coordinateDifferenceChart_symm_apply D e x)
  have hfs : (f.symm : E → E) = coordinateLeftDifference D e x :=
    funext (coordinateDifferenceChart_apply D e x)
  have hxT : x ∈ f.target := coordinateDifferenceChart_base_mem_source D e hxS
  have hfx : f.symm x = 0 := by rw [hfs,coordinateLeftDifference_self]
  obtain ⟨u,hu⟩ := hxu.ringInverse
  let U : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit u
  have hU : (U : E →L[ℝ] E) = Ring.inverse (coordinateAdjointAverage D e x) := hu
  have hdf : HasFDerivAt (f : E → E) (U : E →L[ℝ] E) (f.symm x) := by
    rw [hf,hU,hfx]
    exact hxt
  have hcf : ContDiffAt ℝ ∞ (f : E → E) (f.symm x) := by rw [hf,hfx]; exact htx
  have h := f.contDiffAt_symm hxT hdf hcf
  rw [hfs] at h
  exact h

end DirectedCycles.GleasonLieAlgebra
