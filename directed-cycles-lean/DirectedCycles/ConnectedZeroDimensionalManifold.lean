import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false
namespace DirectedCycles

/-- A charted space over a one-point model space is discrete. -/
theorem chartedSpace_discrete_of_subsingleton_model {E H : Type*}
    [TopologicalSpace E] [Subsingleton E] [TopologicalSpace H] [ChartedSpace E H] :
    DiscreteTopology H := by
  apply discreteTopology_iff_isOpen_singleton.2
  intro x
  have he : (chartAt E x).source = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      exact (chartAt E x).injOn hy (mem_chart_source E x) (Subsingleton.elim _ _)
    · exact Set.singleton_subset_iff.mpr (mem_chart_source E x)
  rw [← he]
  exact (chartAt E x).open_source

/-- The connected zero-dimensional manifold base case has a genuinely
trivial target, derived from its charts and dimension. -/
theorem connected_manifold_subsingleton_of_finrank_zero {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [ChartedSpace E H] [PreconnectedSpace H]
    (hdim : Module.finrank ℝ E = 0) : Subsingleton H := by
  let : Subsingleton E := (Module.finrank_eq_zero_iff_of_free ℝ E).1 hdim
  let : DiscreteTopology H := chartedSpace_discrete_of_subsingleton_model (E := E)
  exact subsingleton_of_preconnected_totallyDisconnected
end DirectedCycles
