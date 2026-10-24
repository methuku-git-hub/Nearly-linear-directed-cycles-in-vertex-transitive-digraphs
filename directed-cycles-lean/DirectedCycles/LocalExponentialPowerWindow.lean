import DirectedCycles.LocalExponentialRadialLaw
import DirectedCycles.LocalExponentialBallTopology

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
namespace LocalExponentialData
variable {H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E H] {Q : LocalGroupAlgebra H} (D : LocalExponentialData (E := E) Q)

include D in
/-- Every prescribed identity neighbourhood contains an open exponential
window whose first N actual powers all remain in that neighbourhood. -/
theorem exists_power_window (W : Set H) (hW : W ∈ 𝓝 Q.one) (N : ℕ) :
    ∃ O : Set H, IsOpen O ∧ Q.one ∈ O ∧ O ⊆ W ∧
      ∀ x ∈ O, ∃ p : Q.PowerSegment x N, ∀ n ≤ N, p.power n ∈ W := by
  have hpre : D.chart ⁻¹' W ∈ 𝓝 (0 : E) := by
    apply (D.chart.continuousAt D.zero_mem).preimage_mem_nhds
    simpa only [D.zero] using hW
  obtain ⟨δ,hδ,hδW⟩ := Metric.mem_nhds_iff.mp hpre
  let r := min D.radius δ
  have hr : 0 < r := lt_min D.radius_pos hδ
  let ε := r/(2*((N : ℝ)+1))
  have hε : 0 < ε := div_pos hr (by positivity)
  have hεr : ε < r := by
    dsimp only [ε]
    apply (div_lt_iff₀ (by positivity)).2
    have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    nlinarith
  let O := D.chart '' Metric.ball (0 : E) ε
  have hOW : O ⊆ W := by
    rintro x ⟨v,hv,rfl⟩
    exact hδW ((Metric.ball_subset_ball (hεr.le.trans (min_le_right _ _))) hv)
  refine ⟨O,D.ball_open (hεr.le.trans (min_le_left _ _)),
    ⟨0,by simpa only [Metric.mem_ball,dist_self] using hε,D.zero⟩,hOW,?_⟩
  rintro x ⟨v,hv,rfl⟩
  have hvn : ‖v‖ < ε := by simpa only [Metric.mem_ball,dist_zero_right] using hv
  have hsize : (N : ℝ)*‖v‖ < r := by
    have hh := (lt_div_iff₀ (show 0 < 2*((N : ℝ)+1) by positivity)).1 hvn
    have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    nlinarith [norm_nonneg v]
  let p : Q.PowerSegment (D.chart v) N := {
    power := fun n => D.chart ((n : ℝ) • v)
    product := D.product_replicate v (hsize.trans_le (min_le_left _ _)) }
  refine ⟨p,?_⟩
  intro n hn
  change D.chart ((n : ℝ) • v) ∈ W
  apply hδW
  rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hnr : (n : ℝ) ≤ N := by exact_mod_cast hn
  exact ((mul_le_mul_of_nonneg_right hnr (norm_nonneg v)).trans_lt hsize).trans_le (min_le_right _ _)
end LocalExponentialData
end DirectedCycles
