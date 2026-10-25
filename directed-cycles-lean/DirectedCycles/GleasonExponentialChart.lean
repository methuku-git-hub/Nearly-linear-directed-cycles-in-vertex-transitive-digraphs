module

public import DirectedCycles.GleasonExponentialNeighbourhood
public import DirectedCycles.LocalHomeomorphFromCompactInjection

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace GleasonLieAlgebra
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- The exponential map of the constructed curve space is an actual local
homeomorphism near zero, with the original group topology. -/
theorem exists_exp_chart : ∃ e : OpenPartialHomeomorph (GleasonLieAlgebra D) G,
    (0 : GleasonLieAlgebra D) ∈ e.source ∧ (e : GleasonLieAlgebra D → G) = exp D := by
  let : MetricSpace G := D.compatibleMetric
  apply exists_local_homeomorph_of_compact_injection (continuous_exp D) 0 (exp_locally_injective D)
  intro U hU
  simpa only [exp_zero] using exp_image_mem_nhds D hU

noncomputable def expChart : OpenPartialHomeomorph (GleasonLieAlgebra D) G :=
  (exists_exp_chart D).choose

theorem zero_mem_expChart_source : (0 : GleasonLieAlgebra D) ∈ (expChart D).source :=
  (exists_exp_chart D).choose_spec.1

theorem expChart_coe : (expChart D : GleasonLieAlgebra D → G) = exp D :=
  (exists_exp_chart D).choose_spec.2

theorem one_mem_expChart_target : (1 : G) ∈ (expChart D).target := by
  have h := (expChart D).map_source (zero_mem_expChart_source D)
  simpa only [expChart_coe,exp_zero] using h

end GleasonLieAlgebra
end DirectedCycles
