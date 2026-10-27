module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]

/-- A continuous group curve obeys the genuine coordinate multiplication law
on a sufficiently small parameter interval. -/
theorem group_curve_coordinate_local_law (chart : G → E) (unchart : E → G)
    (V : Set G) (hV : V ∈ 𝓝 (1 : G)) (hleft : ∀ x ∈ V, unchart (chart x) = x)
    (φ : ℝ → G) (h0 : φ 0 = 1) (hc : ContinuousAt φ 0)
    (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) :
    ∃ r : ℝ, 0 < r ∧ ∀ s t : ℝ, |s|+|t| ≤ r →
      chart (φ (s+t)) = chart (unchart (chart (φ s))*unchart (chart (φ t))) := by
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, φ t ∈ V :=
    hc.preimage_mem_nhds (by simpa only [h0] using hV)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hsmall : ∀ t : ℝ, |t| ≤ δ/2 → φ t ∈ V := by
    intro t ht
    apply hball
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using (show |t| < δ by linarith)
  refine ⟨δ/2,by positivity,?_⟩
  intro s t hst
  rw [hleft _ (hsmall s (by linarith [abs_nonneg t])),
    hleft _ (hsmall t (by linarith [abs_nonneg s])),hadd]
end DirectedCycles
