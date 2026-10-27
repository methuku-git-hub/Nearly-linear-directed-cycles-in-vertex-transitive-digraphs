module

public import DirectedCycles.GleasonCoordinates

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- A single global linear speed bound for all curves in fixed linear
coordinates, obtained by scaling a genuine compact-open neighbourhood. -/
theorem exists_coordinate_speed : ∃ A : ℝ, 0 < A ∧ ∀ x : E, ∀ t : ℝ,
    D.gauge ((toOneParameter D (e.symm x)).eval t) ≤ A*‖x‖*|t| := by
  have hx : Tendsto e.symm (𝓝 (0 : E)) (𝓝 0) := by
    simpa only [map_zero] using e.symm.continuous.tendsto 0
  have hsmall := eventually_small_speed D hx (by norm_num : (0 : ℝ) < 1)
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp hsmall
  refine ⟨2/δ,by positivity,?_⟩
  intro x t
  by_cases hx0 : x = 0
  · subst x
    simp only [map_zero,norm_zero,mul_zero,zero_mul]
    exact (D.gauge_one).le
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let c : ℝ := δ/(2*‖x‖)
  have hc : 0 < c := div_pos hδ (by positivity)
  have hcx : ‖c • x‖ = δ/2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    dsimp [c]
    field_simp
  have hmem : c • x ∈ Metric.ball (0 : E) δ := by
    rw [Metric.mem_ball,dist_zero_right,hcx]
    linarith
  have hb := hδb hmem (t/c)
  change D.gauge ((toOneParameter D (e.symm (c • x))).eval (t/c)) ≤ 1*|t/c| at hb
  rw [map_smul] at hb
  change D.gauge ((toOneParameter D (e.symm x)).eval (c*(t/c))) ≤ 1*|t/c| at hb
  rw [mul_div_cancel₀ _ hc.ne',one_mul,abs_div,abs_of_pos hc] at hb
  apply hb.trans_eq
  dsimp [c]
  field_simp

theorem coordinateExp_gauge_bound {A : ℝ}
    (hA : ∀ x : E, ∀ t : ℝ, D.gauge ((toOneParameter D (e.symm x)).eval t) ≤ A*‖x‖*|t|)
    (x : E) : D.gauge (coordinateExp D e x) ≤ A*‖x‖ := by
  change D.gauge ((toOneParameter D (e.symm x)).eval 1) ≤ A*‖x‖
  simpa only [abs_one,mul_one] using hA x 1

end DirectedCycles.GleasonLieAlgebra
