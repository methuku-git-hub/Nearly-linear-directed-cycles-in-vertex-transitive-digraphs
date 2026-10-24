import DirectedCycles.LieExponentialCurve

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- An actual local group curve is the constructed exponential of its tangent
throughout its given multiplication interval, by its exact global extension. -/
theorem local_lie_curve_eq_exponential (γ : ℝ → G) (hγ0 : γ 0 = 1)
    (hγc : ContinuousAt γ 0) {v : E}
    (hγv : HasDerivAt (fun t => (chartAt E (1 : G)) (γ t)-(chartAt E (1 : G)) 1) v 0)
    {r : ℝ} (hr : 0 < r)
    (hadd : ∀ s t : ℝ, |s|+|t| ≤ r → γ (s+t) = γ s*γ t) :
    ∀ t : ℝ, |t| ≤ r → γ t = lieExponential (G := G) (t • v) := by
  obtain ⟨φ,hφ0,hφadd,hagree⟩ := exists_local_curve_extension γ hγ0 hr hadd
  have heq : φ =ᶠ[𝓝 (0 : ℝ)] γ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
    exact hagree t (le_of_lt (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht))
  have hφc : ContinuousAt φ 0 := hγc.congr_of_eventuallyEq heq
  have hφv : HasDerivAt (fun t => (chartAt E (1 : G)) (φ t)-(chartAt E (1 : G)) 1) v 0 := by
    apply hγv.congr_of_eventuallyEq
    filter_upwards [heq] with t ht
    rw [ht]
  intro t ht
  rw [← hagree t ht]
  exact lie_one_parameter_eq_exponential φ hφ0 hφc hφadd hφv t
end DirectedCycles
