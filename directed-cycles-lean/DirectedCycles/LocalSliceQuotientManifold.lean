module

public import DirectedCycles.LocalSliceQuotientHomeomorph
public import Mathlib.Geometry.Manifold.IsManifold.Basic

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles.LocalNormalSet
variable {H F : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P V W : Set H} (hP : LocalNormalSet P V)
    (hW1 : (1 : H) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

/-- The actual local quotient has a single global chart into the open transverse
slice image. This defines its manifold atlas, before any assertion about the
smoothness of its local group operations. -/
noncomputable def sliceChart (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen W) (hWa : W ⊆ a.target)
    (hrel : ∀ x ∈ W, ∀ y ∈ W, x*y⁻¹ ∈ P ↔ (a.symm x).2 = (a.symm y).2) :
    OpenPartialHomeomorph (hP.WindowQuotient hW1 hWi hW6) F := by
  let : Nonempty (hP.WindowQuotient hW1 hWi hW6) := ⟨hP.windowMk hW1 hWi hW6 ⟨1,hW1⟩⟩
  let e := hP.sliceHomeomorph hW1 hWi hW6 a hWo hWa hrel
  have he : Topology.IsOpenEmbedding (fun x => (e x).val) :=
    (isOpen_slice_range a hWo hWa).isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  exact he.toOpenPartialHomeomorph (fun x => (e x).val)

omit [IsTopologicalGroup H] [NormedSpace ℝ F] in
/-- The slice chart covers the entire actual window quotient. -/
theorem sliceChart_source (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen W) (hWa : W ⊆ a.target)
    (hrel : ∀ x ∈ W, ∀ y ∈ W, x*y⁻¹ ∈ P ↔ (a.symm x).2 = (a.symm y).2) :
    (hP.sliceChart hW1 hWi hW6 a hWo hWa hrel).source = Set.univ := rfl

omit [IsTopologicalGroup H] [NormedSpace ℝ F] in
/-- The actual quotient chart sends each representative to its transverse coordinate. -/
theorem sliceChart_windowMk (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen W) (hWa : W ⊆ a.target)
    (hrel : ∀ x ∈ W, ∀ y ∈ W, x*y⁻¹ ∈ P ↔ (a.symm x).2 = (a.symm y).2) (x : W) :
    (hP.sliceChart hW1 hWi hW6 a hWo hWa hrel) (hP.windowMk hW1 hWi hW6 x) =
      (a.symm x.val).2 := rfl

omit [IsTopologicalGroup H] in
/-- The atlas induced by the actual slice chart is a smooth manifold atlas.
Smooth local multiplication and inversion are separate obligations. -/
theorem sliceChart_isManifold (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen W) (hWa : W ⊆ a.target)
    (hrel : ∀ x ∈ W, ∀ y ∈ W, x*y⁻¹ ∈ P ↔ (a.symm x).2 = (a.symm y).2) :
    let cs := (hP.sliceChart hW1 hWi hW6 a hWo hWa hrel).singletonChartedSpace
      (hP.sliceChart_source hW1 hWi hW6 a hWo hWa hrel)
    @IsManifold ℝ _ F _ _ F _ 𝓘(ℝ,F) ∞ (hP.WindowQuotient hW1 hWi hW6) _ cs :=
  (hP.sliceChart hW1 hWi hW6 a hWo hWa hrel).isManifold_singleton
    (hP.sliceChart_source hW1 hWi hW6 a hWo hWa hrel)
end DirectedCycles.LocalNormalSet
