import DirectedCycles.LocalCentralQuotientSliceHomeomorph
import Mathlib.Geometry.Manifold.IsManifold.Basic

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles.LocalGroupAlgebra.CentralQuotientData
variable {H F : Type*} [TopologicalSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : LocalGroupAlgebra H} {P : Set H} (D : L.CentralQuotientData P)

/-- The actual local quotient has a single global chart into the open transverse
slice image. This defines its manifold atlas, before any assertion about the
smoothness of its local group operations. -/
noncomputable def sliceChart (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen D.small) (hWa : D.small ⊆ a.target)
    (hrel : ∀ x y : D.small, D.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2) :
    OpenPartialHomeomorph D.Carrier F := by
  let : Nonempty D.Carrier := ⟨D.project ⟨L.one,D.one_mem⟩⟩
  let e := D.sliceHomeomorph a hWo hWa hrel
  have he : Topology.IsOpenEmbedding (fun x => (e x).val) :=
    (DirectedCycles.LocalNormalSet.isOpen_slice_range a hWo hWa).isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  exact he.toOpenPartialHomeomorph (fun x => (e x).val)

omit [NormedSpace ℝ F] in
/-- The slice chart covers the entire actual window quotient. -/
theorem sliceChart_source (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen D.small) (hWa : D.small ⊆ a.target)
    (hrel : ∀ x y : D.small, D.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2) :
    (D.sliceChart a hWo hWa hrel).source = Set.univ := rfl

omit [NormedSpace ℝ F] in
/-- The actual quotient chart sends each representative to its transverse coordinate. -/
theorem sliceChart_project (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen D.small) (hWa : D.small ⊆ a.target)
    (hrel : ∀ x y : D.small, D.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2) (x : D.small) :
    (D.sliceChart a hWo hWa hrel) (D.project x) =
      (a.symm x.val).2 := rfl

/-- The atlas induced by the actual slice chart is a smooth manifold atlas.
Smooth local multiplication and inversion are separate obligations. -/
theorem sliceChart_isManifold (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen D.small) (hWa : D.small ⊆ a.target)
    (hrel : ∀ x y : D.small, D.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2) :
    let cs := (D.sliceChart a hWo hWa hrel).singletonChartedSpace
      (D.sliceChart_source a hWo hWa hrel)
    @IsManifold ℝ _ F _ _ F _ 𝓘(ℝ,F) ∞ D.Carrier _ cs :=
  (D.sliceChart a hWo hWa hrel).isManifold_singleton
    (D.sliceChart_source a hWo hWa hrel)
end DirectedCycles.LocalGroupAlgebra.CentralQuotientData
