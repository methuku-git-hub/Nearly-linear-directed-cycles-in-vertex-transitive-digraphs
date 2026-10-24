import DirectedCycles.GleasonSmoothDifferences
import DirectedCycles.GleasonRestrictedCharts
import Mathlib.Geometry.Manifold.IsManifold.Basic

set_option autoImplicit false
open Filter Topology
open scoped Topology ContDiff Manifold
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- Every overlap map of the translated small charts is smooth. Its local
formula uses the proved smooth left-difference map and smooth translation. -/
theorem translatedRestrictedChart_transition_contDiffAt {r : ℝ}
    (hreg : ∀ x : E, ‖x‖ < r → x ∈ (coordinateChart D e).source ∧
      ContDiffAt ℝ ∞ (coordinateLeftDifference D e x) x ∧
      ContDiffAt ℝ ∞ (fun y : E => coordinateMul D e (x,y)) 0)
    (g h : G) {x : E}
    (hx : x ∈ ((translatedRestrictedChart D e r g).symm.trans (translatedRestrictedChart D e r h)).source) :
    ContDiffAt ℝ ∞ ((translatedRestrictedChart D e r g).symm.trans (translatedRestrictedChart D e r h)) x := by
  have hx₁ : x ∈ (restrictedCoordinateChart D e r).source := hx.1
  have hxN : ‖x‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hx₁.2
  let a := (translatedRestrictedChart D e r g).symm x
  have ha : a ∈ (translatedRestrictedChart D e r h).source := hx.2
  let y := translatedRestrictedChart D e r h a
  have hyS : y ∈ (restrictedCoordinateChart D e r).source := (translatedRestrictedChart D e r h).map_source ha
  have hyN : ‖y‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hyS.2
  have haT : h⁻¹*(g*coordinateExp D e x) ∈ (restrictedCoordinateChart D e r).target := by
    change h⁻¹*a ∈ (restrictedCoordinateChart D e r).target at ha
    simpa only [a,translatedRestrictedChart_symm_apply] using ha
  have hyE : coordinateExp D e y = h⁻¹*(g*coordinateExp D e x) := by
    have hh := (restrictedCoordinateChart D e r).right_inv haT
    rw [restrictedCoordinateChart_coe,restrictedCoordinateChart_symm_coe] at hh
    simpa only [y,a,translatedRestrictedChart_apply,translatedRestrictedChart_symm_apply] using hh
  have hc : ContDiffAt ℝ ∞ (fun z => coordinateMul D e (y,coordinateLeftDifference D e x z)) x := by
    have hty : ContDiffAt ℝ ∞ (fun z : E => coordinateMul D e (y,z)) (coordinateLeftDifference D e x x) := by
      simpa only [coordinateLeftDifference_self] using (hreg y hyN).2.2
    exact hty.comp x (hreg x hxN).2.1
  apply hc.congr_of_eventuallyEq
  filter_upwards [coordinateLeftDifference_eventually_target D e x] with z hz
  rw [OpenPartialHomeomorph.trans_apply,translatedRestrictedChart_apply,translatedRestrictedChart_symm_apply]
  change coordinateLog D e (h⁻¹*(g*coordinateExp D e z)) =
    coordinateLog D e (coordinateExp D e y*coordinateExp D e (coordinateLeftDifference D e x z))
  have hzE : coordinateExp D e (coordinateLeftDifference D e x z) =
      (coordinateExp D e x)⁻¹*coordinateExp D e z := coordinateExp_log D e hz
  rw [hyE,hzE]
  congr 1
  group

/-- The translated restricted atlas is a genuine smooth manifold atlas
on the supplied group topology. -/
theorem restrictedCoordinateChartedSpace_isManifold (r : ℝ) (hr : 0 < r)
    (hreg : ∀ x : E, ‖x‖ < r → x ∈ (coordinateChart D e).source ∧
      ContDiffAt ℝ ∞ (coordinateLeftDifference D e x) x ∧
      ContDiffAt ℝ ∞ (fun y : E => coordinateMul D e (x,y)) 0) :
    let := restrictedCoordinateChartedSpace D e r hr
    IsManifold 𝓘(ℝ,E) ∞ G := by
  let := restrictedCoordinateChartedSpace D e r hr
  apply isManifold_of_contDiffOn 𝓘(ℝ,E) ∞ G
  intro a b ha hb
  change a ∈ Set.range (translatedRestrictedChart D e r) at ha
  change b ∈ Set.range (translatedRestrictedChart D e r) at hb
  obtain ⟨g,rfl⟩ := ha
  obtain ⟨h,rfl⟩ := hb
  have hs : ContDiffOn ℝ ∞ ((translatedRestrictedChart D e r g).symm.trans (translatedRestrictedChart D e r h))
      ((translatedRestrictedChart D e r g).symm.trans (translatedRestrictedChart D e r h)).source :=
    fun x hx => (translatedRestrictedChart_transition_contDiffAt D e hreg g h hx).contDiffWithinAt
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.comp_id,Function.id_comp,
    Set.preimage_id_eq,Set.range_id,Set.inter_univ,id_eq] using hs

end DirectedCycles.GleasonLieAlgebra
