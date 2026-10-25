module

public import DirectedCycles.LieExponentialLocalCoordinates
public import DirectedCycles.LocalRadialNormControl

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- A genuine exponential coordinate ball supplies exact norm control for
bounded one-parameter curves, including their arbitrary prescribed tangents. -/
theorem lie_exponential_radial_control :
    ∃ R : ℝ, 0 < R ∧ Set.InjOn (lieExponential (G := G) (E := E)) (Metric.ball 0 R) ∧
      ∀ ρ a : ℝ, 0 ≤ ρ → ρ < R → 0 < a → ∀ v : E,
        (∀ t : ℝ, |t| ≤ a → lieExponential (G := G) (t • v) ∈ (lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) ρ) →
        a*‖v‖ ≤ ρ := by
  obtain ⟨e,he0,_,he⟩ := lie_exponential_local_coordinates (G := G) (E := E)
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds he0)
  have hinj : Set.InjOn (lieExponential (G := G) (E := E)) (Metric.ball 0 R) := by
    intro v hv w hw hvw
    apply e.injOn (hball hv) (hball hw)
    rwa [he v (hball hv),he w (hball hw)]
  exact ⟨R,hR,hinj,fun _ _ hρ hρR ha v himage => radial_norm_le_of_bounded_image _ hρ hρR ha hinj v himage⟩
end DirectedCycles
