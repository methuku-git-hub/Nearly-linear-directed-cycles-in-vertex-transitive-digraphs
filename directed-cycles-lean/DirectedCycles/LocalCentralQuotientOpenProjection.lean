import DirectedCycles.LocalCentralQuotientSliceHomeomorph

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles.LocalGroupAlgebra.CentralQuotientData
variable {H F : Type*} [TopologicalSpace H] [TopologicalSpace F]
    {L : LocalGroupAlgebra H} {P : Set H} (D : L.CentralQuotientData P)

/-- The actual quotient projection is continuous by the quotient topology. -/
theorem continuous_project : Continuous D.project := continuous_quot_mk

/-- The actual quotient projection is open, through the constructed transverse
slice homeomorphism and the openness of coordinate projection. -/
theorem isOpenMap_project (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen D.small) (hWa : D.small ⊆ a.target)
    (hrel : ∀ x y : D.small, D.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2) :
    IsOpenMap D.project := by
  let e := D.sliceHomeomorph a hWo hWa hrel
  let f : D.small → Set.range (fun x : D.small => (a.symm x.val).2) :=
    fun x => ⟨(a.symm x.val).2,⟨x,rfl⟩⟩
  have hf : IsOpenMap f := (isOpenMap_local_slice a hWo hWa).subtype_mk (fun x => ⟨x,rfl⟩)
  have he : D.project = e.symm ∘ f := by
    funext x
    apply e.injective
    rw [Function.comp_apply,e.apply_symm_apply]
    rfl
  rw [he]
  exact e.symm.isOpenMap.comp hf
end DirectedCycles.LocalGroupAlgebra.CentralQuotientData
