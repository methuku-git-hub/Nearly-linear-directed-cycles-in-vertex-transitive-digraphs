module

public import DirectedCycles.LocalCentralQuotientSliceManifold
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
open IsManifold
namespace DirectedCycles.LocalGroupAlgebra.CentralQuotientData
variable {H F : Type*} [TopologicalSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : LocalGroupAlgebra H} {P : Set H} (D : L.CentralQuotientData P)
    (a : OpenPartialHomeomorph (ℝ × F) H) (hWo : IsOpen D.small) (hWa : D.small ⊆ a.target)
    (hrel : ∀ x y : D.small, D.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2)

/-- The actual transverse chart gives the fixed atlas used for the quotient
smoothness proofs. -/
noncomputable abbrev sliceChartedSpace : ChartedSpace F D.Carrier :=
  (D.sliceChart a hWo hWa hrel).singletonChartedSpace
    (D.sliceChart_source a hWo hWa hrel)

/-- This fixed quotient atlas is smooth. -/
theorem sliceChartedSpace_isManifold :
    letI := D.sliceChartedSpace a hWo hWa hrel
    IsManifold 𝓘(ℝ,F) ∞ D.Carrier :=
  D.sliceChart_isManifold a hWo hWa hrel

/-- The actual quotient coordinate map is smooth at every quotient point. -/
theorem contMDiff_sliceChart :
    letI := D.sliceChartedSpace a hWo hWa hrel
    ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (D.sliceChart a hWo hWa hrel) := by
  let := D.sliceChartedSpace a hWo hWa hrel
  let := D.sliceChartedSpace_isManifold a hWo hWa hrel
  change ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (D.sliceChart a hWo hWa hrel)
  intro q
  have he : D.sliceChart a hWo hWa hrel ∈
      maximalAtlas 𝓘(ℝ,F) ∞ D.Carrier := chart_mem_maximalAtlas q
  apply contMDiffAt_of_mem_maximalAtlas he
  rw [D.sliceChart_source]
  exact Set.mem_univ _

/-- The inverse quotient coordinate map is smooth throughout its actual target. -/
theorem contMDiffOn_sliceChart_symm :
    letI := D.sliceChartedSpace a hWo hWa hrel
    ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (D.sliceChart a hWo hWa hrel).symm
      (D.sliceChart a hWo hWa hrel).target := by
  let := D.sliceChartedSpace a hWo hWa hrel
  let := D.sliceChartedSpace_isManifold a hWo hWa hrel
  have he : D.sliceChart a hWo hWa hrel ∈
      maximalAtlas 𝓘(ℝ,F) ∞ D.Carrier :=
    chart_mem_maximalAtlas (D.project ⟨L.one,D.one_mem⟩)
  change ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (D.sliceChart a hWo hWa hrel).symm
    (D.sliceChart a hWo hWa hrel).target
  intro z hz
  exact (contMDiffAt_symm_of_mem_maximalAtlas he hz).contMDiffWithinAt
end DirectedCycles.LocalGroupAlgebra.CentralQuotientData
