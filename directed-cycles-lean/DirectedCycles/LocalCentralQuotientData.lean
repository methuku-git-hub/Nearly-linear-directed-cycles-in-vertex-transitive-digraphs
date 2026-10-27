module

public import DirectedCycles.LocalWindowQuotientProperties
public import DirectedCycles.LocalCentralEquivalence

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Actual windows and an actual local equivalence for quotienting by P.
The relation is exactly membership of an actual relative difference in P. -/
structure CentralQuotientData (P : Set G) where
  large : Set G
  small : Set G
  small_subset : small ⊆ large
  one_mem : L.one ∈ small
  inv_mem : ∀ x ∈ small, L.inv x ∈ small
  domain : L.AllProductsDefined small 3
  cube_subset : L.wordPower small 3 ⊆ large
  equivalence : L.EquivalenceWindow large
  relation_iff : ∀ a b : small, equivalence.Rel a.val b.val ↔ ∃ p ∈ P, L.mulRel a.val (L.inv b.val) p

namespace CentralQuotientData
variable {L} {P : Set G} (D : L.CentralQuotientData P)

abbrev Carrier := D.equivalence.Carrier D.small_subset

abbrev project (a : D.small) : D.Carrier := D.equivalence.project D.small_subset a

theorem project_eq_iff (a b : D.small) :
    D.project a = D.project b ↔ D.equivalence.Rel a.val b.val := Quotient.eq

def algebra : LocalGroupAlgebra D.Carrier :=
  D.equivalence.algebra D.small_subset D.one_mem D.inv_mem D.domain D.cube_subset

def projectionHom : LocalGroupHom (L.restrict D.small D.one_mem D.inv_mem) D.algebra :=
  D.equivalence.projectionHom D.small_subset D.one_mem D.inv_mem D.domain D.cube_subset

noncomputable def finiteImage (B : Finset G) : Finset D.Carrier :=
  D.equivalence.finiteImage D.small_subset B

theorem finiteImage_approximate {K : ℕ} {B : Finset G}
    (hB : IsLocalFiniteApproximateGroup L K B)
    (hsmall : ∀ n ≤ 200, L.wordPower (B : Set G) n ⊆ D.small) :
    IsLocalFiniteApproximateGroup D.algebra K (D.finiteImage B) :=
  D.equivalence.finiteImage_approximate D.small_subset D.one_mem D.inv_mem D.domain D.cube_subset hB hsmall

theorem finiteImage_card_bound (hc : L.Cancellative) (B R : Finset G)
    (hB : (B : Set G) ⊆ D.small) (hP : P ⊆ (R : Set G)) :
    B.card ≤ (D.finiteImage B).card * R.card := by
  apply D.equivalence.finiteImage_card_bound D.small_subset hc B R hB
  intro a b hab
  obtain ⟨p,hp,hm⟩ := (D.relation_iff a b).1 hab
  exact ⟨p,hP hp,hm⟩

theorem algebra_divisionClosed (hd : L.DivisionClosed) : D.algebra.DivisionClosed :=
  D.equivalence.algebra_divisionClosed D.small_subset D.one_mem D.inv_mem D.domain D.cube_subset hd

theorem algebra_reversible (hr : L.Reversible) : D.algebra.Reversible :=
  D.equivalence.algebra_reversible D.small_subset D.one_mem D.inv_mem D.domain D.cube_subset hr
theorem algebra_cancellative (hd : L.DivisionClosed) (hr : L.Reversible) : D.algebra.Cancellative :=
  DivisionClosed.cancellative _ (D.algebra_divisionClosed hd) (D.algebra_reversible hr)
end CentralQuotientData
end LocalGroupAlgebra
end DirectedCycles
