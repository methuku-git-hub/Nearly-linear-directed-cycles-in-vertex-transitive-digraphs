import DirectedCycles.CompactFiniteRepresentation
import DirectedCycles.CompactRegularRepresentation
import Mathlib.MeasureTheory.Measure.Haar.Basic

set_option autoImplicit false
open MeasureTheory
namespace DirectedCycles

/-- Every compact Hausdorff topological group has arbitrarily small
compact normal subgroups whose actual quotients have no small subgroups.
The proof constructs Haar measure, the faithful regular Hilbert action,
compact averaged operators and finite-dimensional separating restrictions. -/
theorem compact_nss_approximation (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] : HasCompactNSSApproximation G := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let K : TopologicalSpace.PositiveCompacts G := ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩
  let μ := Measure.haarMeasure K
  let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  exact compact_nss_of_faithful_hilbert_action μ (leftRegularRepresentation μ)
    (leftRegularRepresentation_continuous μ) (leftRegularRepresentation_inner μ)
    (leftRegularRepresentation_faithful μ)
end DirectedCycles
