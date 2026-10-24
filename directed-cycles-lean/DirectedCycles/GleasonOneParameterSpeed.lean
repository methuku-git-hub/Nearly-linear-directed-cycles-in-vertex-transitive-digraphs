import DirectedCycles.GleasonOneParameterWindow

set_option autoImplicit false
namespace DirectedCycles
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- Every actual one-parameter subgroup has a positive global speed bound
for the constructed compatible metric. -/
theorem oneParameter_exists_speed (φ : OneParameter G) :
    ∃ L : ℝ, 0 < L ∧ ∀ t : ℝ, D.gauge (φ.eval t) ≤ L*|t| := by
  have hC := D.constant_pos
  let R := 1/(D.constant*(D.constant+1))
  have hR : 0 < R := by dsimp [R]; positivity
  have hscale : (D.constant+1)*R ≤ 1/D.constant := by
    apply le_of_eq
    dsimp [R]
    field_simp
  obtain ⟨T,hT,hφ⟩ := D.oneParameter_exists_window φ hR
  refine ⟨2*D.constant*R/T,by positivity,?_⟩
  exact D.oneParameter_gauge_bound φ hT hR.le hscale hφ
end GleasonMetricData
end DirectedCycles
