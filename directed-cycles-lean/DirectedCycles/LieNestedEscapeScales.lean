import DirectedCycles.NestedTangentScaleBounds

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- The actual first-exit curves in nested exponential balls have comparable
scales. This makes the convex-ball comparison quantitative and allows a
negative central direction elsewhere without changing the positive scale ratio. -/
theorem lie_nested_escape_scales {R r δ t : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hR : (1001/1000)*r < R) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hinj : Set.InjOn (lieExponential (G := G) (E := E)) (Metric.ball 0 R))
    (φ ψ : ℝ → G) (hφ0 : φ 0 = 1) (hψ0 : ψ 0 = 1)
    (hφc : ContinuousAt φ 0) (hψc : ContinuousAt ψ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (hψadd : ∀ s t : ℝ, ψ (s+t) = ψ s*ψ t)
    {v w : E}
    (hφv : HasDerivAt (fun t => chartAt E (1 : G) (φ t)-chartAt E (1 : G) 1) v 0)
    (hψw : HasDerivAt (fun t => chartAt E (1 : G) (ψ t)-chartAt E (1 : G) 1) w 0)
    (he : φ 1 = ψ t)
    (hv : δ*r ≤ ‖v‖ ∧ ‖v‖ ≤ (1001/1000)*δ*r)
    (hw : r ≤ ‖w‖ ∧ ‖w‖ ≤ (1001/1000)*r) :
    (99/100)*δ < t ∧ t < (101/100)*δ := by
  have hvR : ‖v‖ < R := by
    have hh := mul_le_mul_of_nonneg_right hδ1 (show 0 ≤ (1001/1000)*r by positivity)
    nlinarith [hv.2]
  have htw : |t| * ‖w‖ < R := by
    rw [abs_of_nonneg ht.1]
    have hh := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg w)
    nlinarith [hw.2]
  have heq := (lie_curve_coordinate_comparison hinj φ ψ hφ0 hψ0 hφc hψc hφadd hψadd
    hφv hψw he hvR htw).1
  have hb := nested_tangent_scale_bounds ht.1 heq hr hv hw
  have he₁ : δ*r/((1001/1000)*r) = (1000/1001)*δ := by field_simp
  have he₂ : ((1001/1000)*δ*r)/r = (1001/1000)*δ := by field_simp
  rw [he₁,he₂] at hb
  constructor <;> nlinarith [hb.1,hb.2]
end DirectedCycles
