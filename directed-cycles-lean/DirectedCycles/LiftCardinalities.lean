module

public import DirectedCycles.BaselineClosureCongruence
public import Mathlib.GroupTheory.Index

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The two normal quotients give the exact three-factor group-order identity. -/
theorem elementClosure_card_factorization {G : Type*} [Group G] [Finite G] (a : G) :
    Nat.card G = Nat.card (G ⧸ elementClosure a) *
      Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)) *
      Nat.card (elementCommutators a) := by
  have h1 := (elementClosure a).index_mul_card
  have h2 := ((elementCommutators a).subgroupOf (elementClosure a)).index_mul_card
  rw [Subgroup.index_eq_card] at h1 h2
  have he := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show elementCommutators a ≤ elementClosure a from le_sup_right)).toEquiv
  rw [he] at h2
  rw [← h1,← h2,Nat.mul_assoc]

/-- The index inside B is the ratio of B's order and the actual C-order,
without assuming C normal. -/
theorem subgroupOf_index_card {G : Type*} [Group G] [Finite G]
    (B C : Subgroup G) (hC : C ≤ B) :
    Nat.card B = (C.subgroupOf B).index * Nat.card C := by
  have h := (C.subgroupOf B).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv] at h
  exact h.symm

end DirectedCycles
