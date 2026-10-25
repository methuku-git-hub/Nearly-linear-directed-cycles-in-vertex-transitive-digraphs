module

public import DirectedCycles.GleasonOneParameterWindow
public import Mathlib.Topology.Order.Compact

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- Gauge convergence is convergence to the identity in the given topology. -/
theorem tendsto_one_of_gauge {ι : Type*} {l : Filter ι} {f : ι → G}
    (h : Tendsto (fun i => D.gauge (f i)) l (𝓝 (0 : ℝ))) :
    Tendsto f l (𝓝 (1 : G)) := by
  let : MetricSpace G := D.compatibleMetric
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := h.eventually (gt_mem_nhds hε)
  filter_upwards [he] with i hi
  change D.metric.dist (f i) 1 < ε
  rw [D.metric.dist_comm]
  exact hi

/-- Actual nearest points in a compact identity-containing set produce
nontrivial residuals tending to the identity, with the minimum-distance
inequality retained for every competing point of that compact set. -/
theorem exists_compact_nearest_residual {ι : Type*} {l : Filter ι}
    {V : Set G} (hV : IsCompact V) (hV1 : (1 : G) ∈ V)
    (g : ι → G) (hgo : ∀ i, g i ∉ V) (hg : Tendsto g l (𝓝 (1 : G))) :
    ∃ h k : ι → G,
      (∀ i, h i ∈ V ∧ k i = (h i)⁻¹*g i ∧ k i ≠ 1 ∧
        D.gauge (k i) ≤ D.gauge (g i) ∧ D.gauge (h i) ≤ 2*D.gauge (g i) ∧
        ∀ v ∈ V, D.gauge (k i) ≤ D.metric.dist (g i) v) ∧
      Tendsto h l (𝓝 (1 : G)) ∧ Tendsto k l (𝓝 (1 : G)) := by
  let : MetricSpace G := D.compatibleMetric
  have hex : ∀ i : ι, ∃ x ∈ V, ∀ y ∈ V, dist (g i) x ≤ dist (g i) y := by
    intro i
    exact hV.exists_isMinOn ⟨1,hV1⟩ (continuous_const.dist continuous_id).continuousOn
  choose h hh hmin using hex
  let k : ι → G := fun i => (h i)⁻¹*g i
  have hkdist : ∀ i, D.gauge (k i) = D.metric.dist (g i) (h i) := by
    intro i
    rw [D.metric.dist_comm,D.dist_eq_gauge]
  have hkb : ∀ i, D.gauge (k i) ≤ D.gauge (g i) := by
    intro i
    rw [hkdist]
    have hi := hmin i 1 hV1
    simpa only [dist_comm,gauge] using hi
  have hhb : ∀ i, D.gauge (h i) ≤ 2*D.gauge (g i) := by
    intro i
    have hi := D.metric.dist_triangle 1 (g i) (h i)
    rw [← hkdist] at hi
    change D.gauge (h i) ≤ D.gauge (g i)+D.gauge (k i) at hi
    linarith [hkb i]
  have hν : Tendsto (fun i => D.gauge (g i)) l (𝓝 (0 : ℝ)) := by
    simpa only [D.gauge_one,Function.comp_def] using D.continuous_gauge.tendsto 1 |>.comp hg
  have hkzero : Tendsto (fun i => D.gauge (k i)) l (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun i => D.gauge_nonneg (k i)) hkb hν
  have hhzero : Tendsto (fun i => D.gauge (h i)) l (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun i => D.gauge_nonneg (h i)) hhb
      (by simpa only [mul_zero] using (tendsto_const_nhds (x := (2 : ℝ))).mul hν)
  refine ⟨h,k,?_,D.tendsto_one_of_gauge hhzero,D.tendsto_one_of_gauge hkzero⟩
  intro i
  refine ⟨hh i,rfl,?_,hkb i,hhb i,?_⟩
  · intro he
    have heq : h i = g i := inv_mul_eq_one.mp he
    exact hgo i (heq ▸ hh i)
  · intro v hv
    rw [hkdist]
    exact hmin i v hv
end GleasonMetricData
end DirectedCycles
