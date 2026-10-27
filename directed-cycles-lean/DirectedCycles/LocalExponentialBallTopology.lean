module

public import DirectedCycles.LocalExponentialRadialLaw
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
namespace LocalExponentialData
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] {L : LocalGroupAlgebra G} (D : LocalExponentialData (E := E) L)

theorem ball_open {r : ℝ} (hr : r ≤ D.radius) : IsOpen (D.chart '' Metric.ball (0 : E) r) :=
  D.chart.isOpen_image_of_subset_source Metric.isOpen_ball ((Metric.ball_subset_ball hr).trans D.ball_source)

theorem closedBall_inv_mem {r : ℝ} (hr : 2*r < D.radius) {x : G}
    (hx : x ∈ D.chart '' Metric.closedBall (0 : E) r) : L.inv x ∈ D.chart '' Metric.closedBall (0 : E) r := by
  obtain ⟨v,hv,rfl⟩ := hx
  have hvn : ‖v‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  refine ⟨-v,?_,D.inv_chart (by linarith)⟩
  simpa only [Metric.mem_closedBall,dist_zero_right,norm_neg] using hv

/-- Compact inner and open outer exponential balls fit inside each prescribed
local model neighbourhood, and the inner balls are exactly inverse closed. -/
theorem ball_sandwich [FiniteDimensional ℝ E] (W : Set G) (hW : W ∈ 𝓝 L.one) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      IsCompact (D.chart '' Metric.closedBall (0 : E) r) ∧
      IsOpen (D.chart '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r)) ∧
      D.chart '' Metric.closedBall (0 : E) r ⊆ D.chart '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r) ∧
      D.chart '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r) ⊆ W ∧
      (∀ x ∈ D.chart '' Metric.closedBall (0 : E) r, L.inv x ∈ D.chart '' Metric.closedBall (0 : E) r) := by
  have hpre : D.chart ⁻¹' W ∈ 𝓝 (0 : E) := by
    apply (D.chart.continuousAt D.zero_mem).preimage_mem_nhds
    simpa only [D.zero] using hW
  obtain ⟨Rw,hRw,hw⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨min D.radius Rw/4,div_pos (lt_min D.radius_pos hRw) (by norm_num),?_⟩
  intro r hr hrr
  have hscale : 4*r < min D.radius Rw := by linarith [(lt_div_iff₀ (show (0 : ℝ) < 4 by norm_num)).1 hrr]
  have hrd : 4*r < D.radius := hscale.trans_le (min_le_left _ _)
  have hrw : (1001/1000 : ℝ)*r < Rw := by have := hscale.trans_le (min_le_right _ _); linarith
  have hsub : Metric.closedBall (0 : E) r ⊆ D.chart.source :=
    (Metric.closedBall_subset_ball (by linarith : r < D.radius)).trans D.ball_source
  refine ⟨(isCompact_closedBall (0 : E) r).image_of_continuousOn (D.chart.continuousOn.mono hsub),
    D.ball_open (by linarith),Set.image_mono (Metric.closedBall_subset_ball (by linarith)),?_,?_⟩
  · rintro x ⟨v,hv,rfl⟩
    exact hw ((Metric.ball_subset_ball hrw.le) hv)
  · exact fun _ hx => D.closedBall_inv_mem (by linarith) hx
end LocalExponentialData
end DirectedCycles
