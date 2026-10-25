module

public import DirectedCycles.LocalExponentialRadialLaw
public import DirectedCycles.LocalWordPowers

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
namespace LocalExponentialData
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] {L : LocalGroupAlgebra G} (D : LocalExponentialData (E := E) L)

/-- If both the first and Nth actual powers lie in a bounded exponential
window, its coordinate shrinks by N. Every radial product and both uses of
chart injectivity lie inside the certified source. -/
theorem power_test {B : Set G} {b : ℝ} (hb : 0 ≤ b) {N : ℕ} (hN : 1 ≤ N)
    (hsize : (N : ℝ)*b < D.radius)
    (hB : B ⊆ D.chart '' Metric.closedBall (0 : E) b) (x : G)
    (hx1 : L.PowerIn B x 1) (hxN : L.PowerIn B x N) :
    ∃ v : E, D.chart v = x ∧ (N : ℝ)*‖v‖ ≤ b := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbR : b < D.radius := by nlinarith
  obtain ⟨x',hx',hp1⟩ := hx1
  have hex : x' = x := (LocalGroupAlgebra.Product.singleton_iff L).1
    (by simpa only [List.replicate_one] using hp1)
  obtain ⟨v,hv,he⟩ := hB (hex ▸ hx')
  have hvn : ‖v‖ ≤ b := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  obtain ⟨y,hy,hpN⟩ := hxN
  obtain ⟨w,hw,hew⟩ := hB hy
  have hwn : ‖w‖ ≤ b := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
  have hvN : (N : ℝ)*‖v‖ < D.radius :=
    (mul_le_mul_of_nonneg_left hvn (Nat.cast_nonneg N)).trans_lt hsize
  have hrad : L.Product (List.replicate N x) (D.chart ((N : ℝ) • v)) := by
    simpa only [he] using D.product_replicate v hvN N le_rfl
  have hNv : (N : ℝ) • v ∈ D.chart.source := D.ball_source (by
    simpa only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)] using hvN)
  have hwS : w ∈ D.chart.source := D.ball_source (by
    simpa only [Metric.mem_ball,dist_zero_right] using hwn.trans_lt hbR)
  have heq : (N : ℝ) • v = w := D.chart.injOn hNv hwS ((hrad.unique L hpN).trans hew.symm)
  have hnorm := congrArg norm heq
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)] at hnorm
  exact ⟨v,he,hnorm ▸ hwn⟩
end LocalExponentialData
end DirectedCycles
