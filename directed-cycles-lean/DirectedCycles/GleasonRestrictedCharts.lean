import DirectedCycles.GleasonDifferenceChart

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- Restrict the actual identity chart to a prescribed coordinate ball. -/
noncomputable def restrictedCoordinateChart (r : ℝ) : OpenPartialHomeomorph E G :=
  (coordinateChart D e).restrOpen (Metric.ball 0 r) Metric.isOpen_ball

theorem restrictedCoordinateChart_coe (r : ℝ) :
    (restrictedCoordinateChart D e r : E → G) = coordinateExp D e := coordinateChart_coe D e

theorem restrictedCoordinateChart_symm_coe (r : ℝ) :
    ((restrictedCoordinateChart D e r).symm : G → E) = coordinateLog D e := rfl

theorem restrictedCoordinateChart_source (r : ℝ) :
    (restrictedCoordinateChart D e r).source = (coordinateChart D e).source ∩ Metric.ball 0 r := rfl

theorem restrictedCoordinateChart_zero_mem_source {r : ℝ} (hr : 0 < r) :
    (0 : E) ∈ (restrictedCoordinateChart D e r).source :=
  ⟨zero_mem_coordinateChart_source D e,Metric.mem_ball_self hr⟩

theorem restrictedCoordinateChart_one_mem_target {r : ℝ} (hr : 0 < r) :
    (1 : G) ∈ (restrictedCoordinateChart D e r).target := by
  have h := (restrictedCoordinateChart D e r).map_source (restrictedCoordinateChart_zero_mem_source D e hr)
  simpa only [restrictedCoordinateChart_coe,coordinateExp_zero] using h

/-- Translated restricted charts, all on the original group topology. -/
noncomputable def translatedRestrictedChart (r : ℝ) (g : G) : OpenPartialHomeomorph G E :=
  (Homeomorph.mulLeft g⁻¹).transOpenPartialHomeomorph (restrictedCoordinateChart D e r).symm

theorem translatedRestrictedChart_apply (r : ℝ) (g h : G) :
    translatedRestrictedChart D e r g h = coordinateLog D e (g⁻¹*h) := rfl

theorem translatedRestrictedChart_symm_apply (r : ℝ) (g : G) (x : E) :
    (translatedRestrictedChart D e r g).symm x = g*coordinateExp D e x := by
  change (g⁻¹)⁻¹*((restrictedCoordinateChart D e r) x) = _
  rw [inv_inv,restrictedCoordinateChart_coe]

theorem translatedRestrictedChart_target (r : ℝ) (g : G) :
    (translatedRestrictedChart D e r g).target = (restrictedCoordinateChart D e r).source := rfl

theorem translatedRestrictedChart_self (r : ℝ) (g : G) :
    translatedRestrictedChart D e r g g = 0 := by
  rw [translatedRestrictedChart_apply,inv_mul_cancel,coordinateLog_one]

theorem translatedRestrictedChart_mem_source {r : ℝ} (hr : 0 < r) (g : G) :
    g ∈ (translatedRestrictedChart D e r g).source := by
  change g⁻¹*g ∈ (restrictedCoordinateChart D e r).target
  rw [inv_mul_cancel]
  exact restrictedCoordinateChart_one_mem_target D e hr

@[instance_reducible]
noncomputable def restrictedCoordinateChartedSpace (r : ℝ) (hr : 0 < r) : ChartedSpace E G where
  atlas := Set.range (translatedRestrictedChart D e r)
  chartAt := translatedRestrictedChart D e r
  mem_chart_source := translatedRestrictedChart_mem_source D e hr
  chart_mem_atlas g := Set.mem_range_self g

end DirectedCycles.GleasonLieAlgebra
