module

public import DirectedCycles.LocalCentralQuotientData

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G : Type*} {L : LocalGroupAlgebra G} {P : Set G} (D : L.CentralQuotientData P)

/-- The upper volume bound uses the actual finite central progression as
a fibre bound and a verified containing target set. -/
theorem finiteImage_card_bound_of_target (hc : L.Cancellative)
    (B R : Finset G) (Q : Finset D.Carrier) (hB : (B : Set G) ⊆ D.small)
    (hP : P ⊆ R) (hQ : ∀ x : D.small, x.val ∈ B → D.project x ∈ Q) :
    B.card ≤ Q.card*R.card := by
  classical
  have hs : D.finiteImage B ⊆ Q := by
    intro y hy
    change y ∈ (B.subtype (· ∈ D.small)).image D.project at hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hQ x (Finset.mem_subtype.mp hx)
  exact (D.finiteImage_card_bound hc B R hB hP).trans
    (Nat.mul_le_mul_right R.card (Finset.card_le_card hs))
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
