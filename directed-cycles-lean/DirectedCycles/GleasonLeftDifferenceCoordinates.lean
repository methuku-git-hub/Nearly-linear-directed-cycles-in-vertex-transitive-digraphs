import DirectedCycles.GleasonAveragedDifferenceEstimate
import DirectedCycles.GleasonCoordinateQuadratic

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- The actual left group difference, expressed in the constructed chart. -/
noncomputable def coordinateLeftDifference (x y : E) : E :=
  coordinateLog D e ((coordinateExp D e x)⁻¹*coordinateExp D e y)

omit [FiniteDimensional ℝ E] in
@[simp] theorem coordinateLeftDifference_self (x : E) : coordinateLeftDifference D e x x = 0 := by
  simp only [coordinateLeftDifference,inv_mul_cancel,coordinateLog_one]

omit [FiniteDimensional ℝ E] in
theorem coordinateLeftDifference_continuousAt (x : E) :
    ContinuousAt (coordinateLeftDifference D e x) x := by
  exact (coordinateLog_continuousAt_one D e).comp_of_eq
    (continuous_const.mul (continuous_coordinateExp D e)).continuousAt (by simp)

omit [FiniteDimensional ℝ E] in
theorem coordinateLeftDifference_continuousAt_zero :
    ContinuousAt (fun p : E × E => coordinateLeftDifference D e p.1 p.2) (0,0) := by
  have hc : Continuous (fun p : E × E => (coordinateExp D e p.1)⁻¹*coordinateExp D e p.2) :=
    ((continuous_coordinateExp D e).comp continuous_fst).inv.mul
      ((continuous_coordinateExp D e).comp continuous_snd)
  exact (coordinateLog_continuousAt_one D e).comp_of_eq hc.continuousAt (by simp)

/-- The coordinate left difference has the actual averaged adjoint as a
first-order approximation, with a uniform quadratic remainder. -/
theorem coordinateLeftDifference_quadratic_error : ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧
    ∀ x y : E, ‖x‖ ≤ δ → ‖y‖ ≤ δ →
      ‖coordinateLeftDifference D e x y-coordinateAdjointAverage D e y (y-x)‖ ≤ K*‖y-x‖^2 := by
  obtain ⟨K,r,hK,hr,herror⟩ := coordinateExp_averaged_difference_error D e
  obtain ⟨a,b,s,ha,_hb,hs,hbi⟩ := exists_coordinateExp_bilipschitz D e
  have hc : Continuous (fun p : E × E => (coordinateExp D e p.1)⁻¹*coordinateExp D e p.2) :=
    ((continuous_coordinateExp D e).comp continuous_fst).inv.mul
      ((continuous_coordinateExp D e).comp continuous_snd)
  have htarget : ∀ᶠ p : E × E in 𝓝 (0,0),
      (coordinateExp D e p.1)⁻¹*coordinateExp D e p.2 ∈ (coordinateChart D e).target := by
    have hn := (coordinateChart D e).open_target.mem_nhds (one_mem_coordinateChart_target D e)
    have hc1 : Tendsto (fun p : E × E => (coordinateExp D e p.1)⁻¹*coordinateExp D e p.2)
        (𝓝 (0,0)) (𝓝 1) := by simpa using hc.tendsto (0,0)
    exact hc1.eventually hn
  have hw : ∀ᶠ p : E × E in 𝓝 (0,0), ‖coordinateLeftDifference D e p.1 p.2‖ < s := by
    have h0 : ‖coordinateLeftDifference D e (0 : E) 0‖ < s := by simpa using hs
    exact (coordinateLeftDifference_continuousAt_zero D e).norm.eventually (gt_mem_nhds h0)
  have hz : ∀ᶠ p : E × E in 𝓝 (0,0), ‖coordinateAdjointAverage D e p.2 (p.2-p.1)‖ < s := by
    have hc' : Continuous (fun p : E × E => coordinateAdjointAverage D e p.2 (p.2-p.1)) :=
      ((coordinateAdjointAverage_contDiff D e).continuous.comp continuous_snd).clm_apply
        (continuous_snd.sub continuous_fst)
    exact hc'.norm.continuousAt.eventually (gt_mem_nhds (by simpa using hs))
  have hnear : ∀ᶠ p : E × E in 𝓝 (0,0),
      (coordinateExp D e p.1)⁻¹*coordinateExp D e p.2 ∈ (coordinateChart D e).target ∧
      ‖coordinateLeftDifference D e p.1 p.2‖ < s ∧ ‖coordinateAdjointAverage D e p.2 (p.2-p.1)‖ < s := by
    filter_upwards [htarget,hw,hz] with p hp hw' hz'
    exact ⟨hp,hw',hz'⟩
  obtain ⟨η,hη,hηB⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min r (η/2)
  have hδ : 0 < δ := lt_min hr (by positivity)
  refine ⟨K/a,δ,by positivity,hδ,?_⟩
  intro x y hx hy
  have hmem : (x,y) ∈ Metric.ball (0 : E × E) η := by
    rw [Metric.mem_ball,dist_zero_right,Prod.norm_def]
    have hδη : δ < η := (min_le_right _ _).trans_lt (by linarith)
    exact max_lt (hx.trans_lt hδη) (hy.trans_lt hδη)
  obtain ⟨ht,hw',hz'⟩ := hηB hmem
  have hl := (hbi (coordinateLeftDifference D e x y) (coordinateAdjointAverage D e y (y-x)) hw'.le hz'.le).1
  have hexp : coordinateExp D e (coordinateLeftDifference D e x y) =
      (coordinateExp D e x)⁻¹*coordinateExp D e y := coordinateExp_log D e ht
  rw [hexp,norm_sub_rev] at hl
  have hh := hl.trans (herror x y (hx.trans (min_le_left _ _)) (hy.trans (min_le_left _ _)))
  have hdivide := (le_div_iff₀ ha).mpr (show
      ‖coordinateLeftDifference D e x y-coordinateAdjointAverage D e y (y-x)‖*a ≤ K*‖y-x‖^2 by nlinarith)
  exact hdivide.trans_eq (by ring)

end DirectedCycles.GleasonLieAlgebra
