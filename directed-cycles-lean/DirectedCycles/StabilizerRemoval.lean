import DirectedCycles.NilpotentRanks
import DirectedCycles.NilpotentOrder
import DirectedCycles.FreeQuotient
import DirectedCycles.NormalClosureExponent

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- The explicit bound for the normal closure used in stabilizer removal. -/
theorem stabilizerClosure_card_bound {G V : Type*} [Group G] [Finite G] [MulAction G V]
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N] (x : V)
    (B r c : ℕ) (hB : Nat.card (MulAction.stabilizer G x) ≤ B)
    (hr : Group.rank N ≤ r) (hc : Group.nilpotencyClass N ≤ c) :
    Nat.card (stabilizerClosure N x) ≤ B ^
      (∑ i ∈ Finset.range c, (∑ j ∈ Finset.range c, r ^ (j + 1)) ^ (i + 1)) := by
  let A := N ⊓ MulAction.stabilizer G x
  let L := stabilizerClosure N x
  let R := ∑ j ∈ Finset.range c, r ^ (j + 1)
  have hLN : L ≤ N := stabilizerClosure_le N x
  let e := Subgroup.subgroupOfEquivOfLe hLN
  have : Group.IsNilpotent L := Group.nilpotent_of_mulEquiv e
  have hLr : Group.rank L ≤ R := by
    rw [← Group.rank_congr e]
    exact nilpotent_subgroup_rank_bound r c hr hc (L.subgroupOf N)
  have hLc : Group.nilpotencyClass L ≤ c :=
    (Group.nilpotencyClass_le_of_surjective e.toMonoidHom e.surjective).trans
      ((Subgroup.nilpotencyClass_le (L.subgroupOf N)).trans hc)
  have hA : Nat.card A ≤ B := (Subgroup.card_le_of_le (show A ≤ MulAction.stabilizer G x from inf_le_right)).trans hB
  have h := nilpotent_order_bound (G := L) R c (Nat.card A) hLr hLc Nat.card_pos
    (normalClosure_abelianization_card_exponent A)
  exact h.trans (Nat.pow_le_pow_left hA _)

/-- Manuscript Lemma 3.9, with its order bound, actual free quotient action,
orbit bound and vertex-count inequality. Quotient rank and class bounds are
included for the later main-theorem application. -/
theorem removing_bounded_stabilizers {G V : Type*} [Group G] [Fintype G] [Fintype V]
    [MulAction G V] (N : Subgroup G) [N.Normal] [Group.IsNilpotent N]
    (x : V) (ht : ∀ u v : V, ∃ g : G, g • u = v)
    (B r c : ℕ) (hB : ∀ v : V, Nat.card (MulAction.stabilizer G v) ≤ B)
    (hr : Group.rank N ≤ r) (hc : Group.nilpotencyClass N ≤ c) :
    ∃ (L : Subgroup G) (hL : L.Normal),
      letI := hL
      L ≤ N ∧ Nat.card L ≤ B ^
        (∑ i ∈ Finset.range c, (∑ j ∈ Finset.range c, r ^ (j + 1)) ^ (i + 1)) ∧
      Group.rank (N ⧸ L.comap N.subtype) ≤ r ∧
      Group.nilpotencyClass (N ⧸ L.comap N.subtype) ≤ c ∧
      ∃ a : MulAction (N ⧸ L.comap N.subtype) (Quotient (MulAction.orbitRel L V)),
        letI := a
        (∀ g : N ⧸ L.comap N.subtype, ∀ q : Quotient (MulAction.orbitRel L V), g • q = q → g = 1) ∧
        Nat.card (Quotient (MulAction.orbitRel (N ⧸ L.comap N.subtype)
          (Quotient (MulAction.orbitRel L V)))) ≤ N.index ∧
        Nat.card V ≤ Nat.card (Quotient (MulAction.orbitRel L V)) * Nat.card L := by
  let L := stabilizerClosure N x
  obtain ⟨hLN, a, hfree, horbit, hsize⟩ := stabilizer_removal_geometry N x ht
  refine ⟨L, inferInstance, hLN, stabilizerClosure_card_bound N x B r c (hB x) hr hc, ?_, ?_,
    a, hfree, horbit, hsize⟩
  · exact (Group.rank_le_of_surjective (QuotientGroup.mk' (L.comap N.subtype))
      (QuotientGroup.mk'_surjective _)).trans hr
  · exact (Group.nilpotencyClass_quotient_le (L.comap N.subtype)).trans hc

end DirectedCycles
