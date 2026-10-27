module

public import DirectedCycles.GleasonProductCoordinateFactorization
public import DirectedCycles.GleasonCoordinateIdentityDerivative

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- The derivative formula assembled from the actual averaged adjoint
and actual conjugation. -/
noncomputable def coordinateMulDerivative (p : E × E) : E × E →L[ℝ] E :=
  (Ring.inverse (coordinateAdjointAverage D e (coordinateMul D e p))).comp
    (((coordinateAdjoint D e ((coordinateExp D e p.2)⁻¹)).comp (coordinateAdjointAverage D e p.1)).comp
      (ContinuousLinearMap.fst ℝ E E)+
      (coordinateAdjointAverage D e p.2).comp (ContinuousLinearMap.snd ℝ E E))

/-- Exact group factorization and the previously derived coordinate
inverse derivative give the full joint multiplication derivative. -/
theorem coordinateMul_hasFDerivAt_of_local_data {x y : E}
    (hbase : coordinateExp D e x*coordinateExp D e y ∈ (coordinateChart D e).target)
    (hx : HasFDerivAt (coordinateLeftDifference D e x) (coordinateAdjointAverage D e x) x)
    (hy : HasFDerivAt (coordinateLeftDifference D e y) (coordinateAdjointAverage D e y) y)
    (hm : HasFDerivAt (fun z : E => coordinateMul D e (coordinateMul D e (x,y),z))
      (Ring.inverse (coordinateAdjointAverage D e (coordinateMul D e (x,y)))) 0) :
    HasFDerivAt (coordinateMul D e) (coordinateMulDerivative D e (x,y)) (x,y) := by
  let Q := coordinateAdjoint D e ((coordinateExp D e y)⁻¹)
  let X := (Q.comp (coordinateAdjointAverage D e x)).comp (ContinuousLinearMap.fst ℝ E E)
  let Y := (coordinateAdjointAverage D e y).comp (ContinuousLinearMap.snd ℝ E E)
  have hX : HasFDerivAt (fun p : E × E => Q (coordinateLeftDifference D e x p.1)) X (x,y) := by
    have h₁ : HasFDerivAt (fun p : E × E => coordinateLeftDifference D e x p.1)
        ((coordinateAdjointAverage D e x).comp (ContinuousLinearMap.fst ℝ E E)) (x,y) :=
      HasFDerivAt.comp (f := fun p : E × E => p.1) (g := coordinateLeftDifference D e x)
        (x,y) hx (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
    have h₂ : HasFDerivAt (fun p : E × E => Q (coordinateLeftDifference D e x p.1))
        (Q.comp ((coordinateAdjointAverage D e x).comp (ContinuousLinearMap.fst ℝ E E))) (x,y) :=
      Q.hasFDerivAt.comp (x,y) h₁
    exact h₂
  have hY : HasFDerivAt (fun p : E × E => coordinateLeftDifference D e y p.2) Y (x,y) :=
    HasFDerivAt.comp (f := fun p : E × E => p.2) (g := coordinateLeftDifference D e y)
      (x,y) hy (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  have hμ : HasFDerivAt (coordinateMul D e)
      (ContinuousLinearMap.fst ℝ E E+ContinuousLinearMap.snd ℝ E E)
      (Q (coordinateLeftDifference D e x x),coordinateLeftDifference D e y y) := by
    simpa only [coordinateLeftDifference_self,map_zero] using coordinateMul_hasFDerivAt_zero D e
  have hi : HasFDerivAt (coordinateProductIncrement D e x y) (X+Y) (x,y) := by
    have h := hμ.comp (x,y) (hX.prodMk hY)
    have he : (ContinuousLinearMap.fst ℝ E E+ContinuousLinearMap.snd ℝ E E).comp (X.prod Y) = X+Y := by
      apply ContinuousLinearMap.ext
      intro p
      rfl
    rw [he] at h
    exact h
  have hm' : HasFDerivAt (fun z : E => coordinateMul D e (coordinateMul D e (x,y),z))
      (Ring.inverse (coordinateAdjointAverage D e (coordinateMul D e (x,y))))
      (coordinateProductIncrement D e x y (x,y)) := by
    simpa only [coordinateProductIncrement_self] using hm
  exact (hm'.comp (x,y) hi).congr_of_eventuallyEq (coordinateMul_increment_eventuallyEq D e hbase)

/-- The full joint derivative formula holds throughout a genuine open
ball, and all averaged operators used as inverses there are units. -/
theorem exists_coordinateMul_derivative_radius : ∃ δ : ℝ, 0 < δ ∧
    ∀ p : E × E, ‖p‖ < δ →
      IsUnit (coordinateAdjointAverage D e (coordinateMul D e p)) ∧
      HasFDerivAt (coordinateMul D e) (coordinateMulDerivative D e p) p := by
  obtain ⟨r,hr,hdata⟩ := exists_coordinate_translation_derivative_radius D e
  have hc : Continuous (fun p : E × E => coordinateExp D e p.1*coordinateExp D e p.2) :=
    ((continuous_coordinateExp D e).comp continuous_fst).mul ((continuous_coordinateExp D e).comp continuous_snd)
  have ht : ∀ᶠ p : E × E in 𝓝 (0,0), coordinateExp D e p.1*coordinateExp D e p.2 ∈ (coordinateChart D e).target := by
    have hc1 : Tendsto (fun p : E × E => coordinateExp D e p.1*coordinateExp D e p.2) (𝓝 (0,0)) (𝓝 1) := by
      simpa only [coordinateExp_zero,one_mul] using hc.tendsto (0,0)
    exact hc1.eventually ((coordinateChart D e).open_target.mem_nhds (one_mem_coordinateChart_target D e))
  have hm : ∀ᶠ p : E × E in 𝓝 (0,0), ‖coordinateMul D e p‖ < r :=
    (coordinateMul_continuousAt_zero D e).norm.eventually (gt_mem_nhds (by simpa only [coordinateMul_zero,norm_zero] using hr))
  have hn : ∀ᶠ p : E × E in 𝓝 (0,0),
      coordinateExp D e p.1*coordinateExp D e p.2 ∈ (coordinateChart D e).target ∧ ‖coordinateMul D e p‖ < r := by
    filter_upwards [ht,hm] with p hp hmp
    exact ⟨hp,hmp⟩
  obtain ⟨s,hs,hsB⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨min r s,lt_min hr hs,?_⟩
  intro p hp
  have hpr : ‖p‖ < r := hp.trans_le (min_le_left _ _)
  have hpS : p ∈ Metric.ball (0 : E × E) s := by
    rw [Metric.mem_ball,dist_zero_right]
    exact hp.trans_le (min_le_right _ _)
  obtain ⟨hbase,hmp⟩ := hsB hpS
  have hx : ‖p.1‖ < r := (show ‖p.1‖ ≤ ‖p‖ by rw [Prod.norm_def]; exact le_max_left _ _).trans_lt hpr
  have hy : ‖p.2‖ < r := (show ‖p.2‖ ≤ ‖p‖ by rw [Prod.norm_def]; exact le_max_right _ _).trans_lt hpr
  exact ⟨(hdata _ hmp).2.1,coordinateMul_hasFDerivAt_of_local_data D e hbase
    (hdata _ hx).2.2.1 (hdata _ hy).2.2.1 (hdata _ hmp).2.2.2⟩

end DirectedCycles.GleasonLieAlgebra
