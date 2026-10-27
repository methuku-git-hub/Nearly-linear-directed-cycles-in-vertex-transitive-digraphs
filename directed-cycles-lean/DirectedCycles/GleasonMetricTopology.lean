module

public import DirectedCycles.GleasonMetricBasics
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Compact

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Topology
namespace DirectedCycles
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- A definitionally compatible presentation of the constructed metric. -/
abbrev compatibleMetric : MetricSpace G := D.metric.replaceTopology D.topology_eq.symm

theorem compatibleMetric_dist (x y : G) : D.compatibleMetric.dist x y = D.metric.dist x y := rfl

theorem compatibleMetric_topology : D.compatibleMetric.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace G) := rfl

/-- A compatible left-invariant metric on a locally compact group is
complete: a Cauchy tail lies in a translate of one compact identity neighbourhood. -/
theorem compatibleMetric_complete [IsTopologicalGroup G] [LocallyCompactSpace G] :
    let := D.compatibleMetric
    CompleteSpace G := by
  let : MetricSpace G := D.compatibleMetric
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨K,hK,hK1⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hK1
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
  let L := (fun x : G => u N*x) '' K
  have hL : IsCompact L := hK.image (continuous_const.mul continuous_id)
  have hmem : ∀ᶠ m in atTop, u m ∈ L := by
    filter_upwards [eventually_ge_atTop N] with m hm
    refine ⟨(u N)⁻¹*u m,?_,by simp⟩
    apply hball
    change D.metric.dist ((u N)⁻¹*u m) 1 < ε
    rw [D.metric.dist_comm]
    change D.gauge ((u N)⁻¹*u m) < ε
    rw [← D.dist_eq_gauge]
    exact hN N le_rfl m hm
  obtain ⟨x,_hx,hlim⟩ := hL.isComplete _ hu (Filter.le_principal_iff.mpr hmem)
  exact ⟨x,hlim⟩
end GleasonMetricData
end DirectedCycles
