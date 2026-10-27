module

public import DirectedCycles.LocalCentralQuotientData
public import DirectedCycles.LocalDivision
public import Mathlib.Data.Fintype.Card

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G : Type*} {L : LocalGroupAlgebra G} {P : Set G} (D : L.CentralQuotientData P)

theorem project_mul {x y z : D.small} (h : L.mulRel x.val y.val z.val) :
    D.algebra.mulRel (D.project x) (D.project y) (D.project z) :=
  ⟨x,y,z,rfl,rfl,rfl,h⟩

/-- Distinct quotient coordinates and distinct kernel coordinates give a
proper product grid when the actual products lie in the quotient window. -/
theorem productGrid_injective (hc : L.Cancellative) {α β : Type*}
    (a : α → D.small) (b : β → D.small) (z : α × β → D.small)
    (ha : Function.Injective (fun i => D.project (a i)))
    (hb : Function.Injective (fun j => (b j).val))
    (hb1 : ∀ j, D.project (b j) = D.algebra.one)
    (hm : ∀ i j, L.mulRel (a i).val (b j).val (z (i,j)).val) :
    Function.Injective (fun ij => (z ij).val) := by
  have hproj : ∀ i j, D.project (z (i,j)) = D.project (a i) := by
    intro i j
    have hh := D.project_mul (hm i j)
    rw [hb1 j] at hh
    exact D.algebra.unique hh (D.algebra.mul_one _)
  rintro ⟨i,j⟩ ⟨i',j'⟩ he
  change (z (i,j)).val = (z (i',j')).val at he
  have heq : z (i,j) = z (i',j') := Subtype.ext he
  have hi : i = i' := ha (by change D.project (a i) = D.project (a i'); rw [← hproj i j,← hproj i' j',heq])
  subst i'
  have hj : j = j' := by
    apply hb
    change (b j).val = (b j').val
    apply hc.left_cancel _ (hm i j')
    rw [← he]
    exact hm i j
  exact Prod.ext rfl hj

/-- A proper central product grid gives its full product-cardinality lower
bound inside any set containing the constructed values. -/
theorem productGrid_card_le (hc : L.Cancellative) {α β : Type*} [Fintype α] [Fintype β]
    (a : α → D.small) (b : β → D.small) (z : α × β → D.small)
    (ha : Function.Injective (fun i => D.project (a i)))
    (hb : Function.Injective (fun j => (b j).val))
    (hb1 : ∀ j, D.project (b j) = D.algebra.one)
    (hm : ∀ i j, L.mulRel (a i).val (b j).val (z (i,j)).val)
    (Q : Finset G) (hQ : ∀ ij, (z ij).val ∈ Q) :
    Fintype.card α * Fintype.card β ≤ Q.card := by
  let f : α × β → Q := fun ij => ⟨(z ij).val,hQ ij⟩
  have hf : Function.Injective f := by
    intro i j he
    apply D.productGrid_injective hc a b z ha hb hb1 hm
    exact congrArg (fun x : Q => x.val) he
  simpa only [Fintype.card_prod,Fintype.card_coe] using Fintype.card_le_of_injective f hf
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
