module

public import DirectedCycles.LocalSliceQuotientManifold
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
open IsManifold
namespace DirectedCycles.LocalNormalSet
variable {H F : Type*} [Group H] [TopologicalSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P V W : Set H} (hP : LocalNormalSet P V)
    (hW1 : (1 : H) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)
    (a : OpenPartialHomeomorph (ℝ × F) H) (hWo : IsOpen W) (hWa : W ⊆ a.target)
    (hrel : ∀ x ∈ W, ∀ y ∈ W, x*y⁻¹ ∈ P ↔ (a.symm x).2 = (a.symm y).2)

/-- The actual transverse chart gives the fixed atlas used for the quotient
smoothness proofs. -/
noncomputable abbrev sliceChartedSpace : ChartedSpace F (hP.WindowQuotient hW1 hWi hW6) :=
  (hP.sliceChart hW1 hWi hW6 a hWo hWa hrel).singletonChartedSpace
    (hP.sliceChart_source hW1 hWi hW6 a hWo hWa hrel)

/-- This fixed quotient atlas is smooth. -/
theorem sliceChartedSpace_isManifold :
    letI := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
    IsManifold 𝓘(ℝ,F) ∞ (hP.WindowQuotient hW1 hWi hW6) :=
  hP.sliceChart_isManifold hW1 hWi hW6 a hWo hWa hrel

/-- The actual quotient coordinate map is smooth at every quotient point. -/
theorem contMDiff_sliceChart :
    letI := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
    ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (hP.sliceChart hW1 hWi hW6 a hWo hWa hrel) := by
  let := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
  let := hP.sliceChartedSpace_isManifold hW1 hWi hW6 a hWo hWa hrel
  change ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (hP.sliceChart hW1 hWi hW6 a hWo hWa hrel)
  intro q
  have he : hP.sliceChart hW1 hWi hW6 a hWo hWa hrel ∈
      maximalAtlas 𝓘(ℝ,F) ∞ (hP.WindowQuotient hW1 hWi hW6) := chart_mem_maximalAtlas q
  apply contMDiffAt_of_mem_maximalAtlas he
  rw [hP.sliceChart_source]
  exact Set.mem_univ _

/-- The inverse quotient coordinate map is smooth throughout its actual target. -/
theorem contMDiffOn_sliceChart_symm :
    letI := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
    ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (hP.sliceChart hW1 hWi hW6 a hWo hWa hrel).symm
      (hP.sliceChart hW1 hWi hW6 a hWo hWa hrel).target := by
  let := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
  let := hP.sliceChartedSpace_isManifold hW1 hWi hW6 a hWo hWa hrel
  have he : hP.sliceChart hW1 hWi hW6 a hWo hWa hrel ∈
      maximalAtlas 𝓘(ℝ,F) ∞ (hP.WindowQuotient hW1 hWi hW6) :=
    chart_mem_maximalAtlas (hP.windowMk hW1 hWi hW6 ⟨1,hW1⟩)
  change ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (hP.sliceChart hW1 hWi hW6 a hWo hWa hrel).symm
    (hP.sliceChart hW1 hWi hW6 a hWo hWa hrel).target
  intro z hz
  exact (contMDiffAt_symm_of_mem_maximalAtlas he hz).contMDiffWithinAt
end DirectedCycles.LocalNormalSet
