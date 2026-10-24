import DirectedCycles.LocalCentralQuotientData
import DirectedCycles.LocalSliceQuotientHomeomorph

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles.LocalGroupAlgebra.CentralQuotientData
variable {H F : Type*} [TopologicalSpace H] [TopologicalSpace F]
    {L : LocalGroupAlgebra H} {P : Set H} (D : L.CentralQuotientData P)

/-- The actual quotient of a local ambient group is homeomorphic to its open
transverse slice image once the actual equivalence is identified. -/
noncomputable def sliceHomeomorph (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen D.small) (hWa : D.small ⊆ a.target)
    (hrel : ∀ x y : D.small, D.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2) :
    D.Carrier ≃ₜ Set.range (fun x : D.small => (a.symm x.val).2) :=
  (Homeomorph.Quotient.congrRight hrel).trans
    (Homeomorph.quotientKerEquivRange ((isOpenMap_local_slice a hWo hWa).isStrictMap
      (continuous_local_slice a hWa)))

/-- Exact projection formula for the constructed local quotient homeomorphism. -/
theorem sliceHomeomorph_project (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen D.small) (hWa : D.small ⊆ a.target)
    (hrel : ∀ x y : D.small, D.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2)
    (x : D.small) :
    ((D.sliceHomeomorph a hWo hWa hrel) (D.project x)).val = (a.symm x.val).2 := rfl
end DirectedCycles.LocalGroupAlgebra.CentralQuotientData
