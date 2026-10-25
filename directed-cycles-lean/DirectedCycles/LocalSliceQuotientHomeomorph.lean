module

public import DirectedCycles.LocalQuotientTopology
public import Mathlib.Topology.Maps.Strict.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
variable {H F : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace F]

omit [Group H] [IsTopologicalGroup H] in
/-- Transverse projection of an actual open coordinate window is continuous. -/
theorem continuous_local_slice (a : OpenPartialHomeomorph (ℝ × F) H)
    {W : Set H} (hWa : W ⊆ a.target) :
    Continuous (fun x : W => (a.symm x.val).2) := by
  apply continuous_snd.comp
  exact a.symm.continuousOn.comp_continuous continuous_subtype_val (fun x => hWa x.property)

omit [Group H] [IsTopologicalGroup H] in
/-- The same transverse projection is open: coordinate inversion and projection
are open on their actual domains. -/
theorem isOpenMap_local_slice (a : OpenPartialHomeomorph (ℝ × F) H)
    {W : Set H} (hWo : IsOpen W) (hWa : W ⊆ a.target) :
    IsOpenMap (fun x : W => (a.symm x.val).2) := by
  intro S hS
  have hOS : IsOpen (Subtype.val '' S : Set H) := hWo.isOpenMap_subtype_val S hS
  have hsubset : (Subtype.val '' S : Set H) ⊆ a.target := by
    rintro x ⟨y,_,rfl⟩
    exact hWa y.property
  have hcoord := a.isOpen_image_symm_of_subset_target hOS hsubset
  have hh := isOpenMap_snd (a.symm '' (Subtype.val '' S)) hcoord
  simpa only [Set.image_image] using hh

namespace LocalNormalSet
variable {P V W : Set H} (hP : LocalNormalSet P V)
    (hW1 : (1 : H) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

/-- Once the actual window equivalence is identified with a transverse slice,
the actual local quotient is homeomorphic to the open slice image. -/
noncomputable def sliceHomeomorph (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen W) (hWa : W ⊆ a.target)
    (hrel : ∀ x ∈ W, ∀ y ∈ W, x*y⁻¹ ∈ P ↔ (a.symm x).2 = (a.symm y).2) :
    hP.WindowQuotient hW1 hWi hW6 ≃ₜ Set.range (fun x : W => (a.symm x.val).2) :=
  (Homeomorph.Quotient.congrRight (fun x y => hrel x.val x.property y.val y.property)).trans
    (Homeomorph.quotientKerEquivRange ((isOpenMap_local_slice a hWo hWa).isStrictMap
      (continuous_local_slice a hWa)))

omit [IsTopologicalGroup H] in
/-- The constructed quotient homeomorphism has the expected projection formula. -/
theorem sliceHomeomorph_windowMk (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen W) (hWa : W ⊆ a.target)
    (hrel : ∀ x ∈ W, ∀ y ∈ W, x*y⁻¹ ∈ P ↔ (a.symm x).2 = (a.symm y).2)
    (x : W) :
    ((hP.sliceHomeomorph hW1 hWi hW6 a hWo hWa hrel) (hP.windowMk hW1 hWi hW6 x)).val =
      (a.symm x.val).2 := rfl

omit [Group H] [IsTopologicalGroup H] in
/-- The slice range is an actual open subset of the transverse space. -/
theorem isOpen_slice_range (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen W) (hWa : W ⊆ a.target) :
    IsOpen (Set.range (fun x : W => (a.symm x.val).2)) :=
  (isOpenMap_local_slice a hWo hWa).isOpen_range
end LocalNormalSet
end DirectedCycles
