import DirectedCycles.StabilizerRemoval
import DirectedCycles.NormalOrbitCycleLift

set_option autoImplicit false
namespace DirectedCycles

/-- Stabilizer removal with the actual quotient graph, its invariant free
action, and the cycle-lifting map. Compatibility is retained explicitly. -/
theorem stabilizer_removal_graph {G V : Type*} [Group G] [Fintype G] [Fintype V] [MulAction G V]
    (X : Digraph V) (hX : ∀ g : G, ∀ x y, X (g • x) (g • y) ↔ X x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (hsc : StronglyConnected X)
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N] (x : V)
    (B r c : ℕ) (hB : ∀ v : V, Nat.card (MulAction.stabilizer G v) ≤ B)
    (hr : Group.rank N ≤ r) (hc : Group.nilpotencyClass N ≤ c) :
    ∃ (L : Subgroup G) (hL : L.Normal),
      letI := hL
      L ≤ N ∧ Nat.card L ≤ B ^
        (∑ i ∈ Finset.range c, (∑ j ∈ Finset.range c, r ^ (j + 1)) ^ (i + 1)) ∧
      Group.rank (N ⧸ L.comap N.subtype) ≤ r ∧
      Group.nilpotencyClass (N ⧸ L.comap N.subtype) ≤ c ∧
      ∃ act : MulAction (N ⧸ L.comap N.subtype) (Quotient (MulAction.orbitRel L V)),
        letI := act
        (∀ g : N ⧸ L.comap N.subtype, ∀ q : Quotient (MulAction.orbitRel L V), g • q = q → g = 1) ∧
        Nat.card (Quotient (MulAction.orbitRel (N ⧸ L.comap N.subtype)
          (Quotient (MulAction.orbitRel L V)))) ≤ N.index ∧
        Nat.card V ≤ Nat.card (Quotient (MulAction.orbitRel L V)) * Nat.card L ∧
        (let Y := QuotientDigraph X (Quotient.mk'' : V → Quotient (MulAction.orbitRel L V))
         StronglyConnected Y ∧
         (∀ g : N ⧸ L.comap N.subtype, ∀ x y, Y (g • x) (g • y) ↔ Y x y) ∧
         ∀ C : Cycle Y, ∃ D : Cycle X, C.length ≤ D.length) := by
  classical
  let L := stabilizerClosure N x
  have hLN : L ≤ N := stabilizerClosure_le N x
  obtain ⟨act,hfree,hcompat⟩ := exists_free_quotient_action N L hLN (normal_stabilizer_le_closure N x ht)
  let : MulAction (N ⧸ L.comap N.subtype) (Quotient (MulAction.orbitRel L V)) := act
  refine ⟨L,inferInstance,hLN,stabilizerClosure_card_bound N x B r c (hB x) hr hc,?_,?_,
    act,hfree,?_,?_,?_,?_,?_⟩
  · exact (Group.rank_le_of_surjective (QuotientGroup.mk' (L.comap N.subtype))
      (QuotientGroup.mk'_surjective _)).trans hr
  · exact (Group.nilpotencyClass_quotient_le (L.comap N.subtype)).trans hc
  · rw [quotient_orbit_card_eq N L hLN act hcompat]
    exact orbit_count_le_index N x ht
  · let : Fintype (Quotient (MulAction.orbitRel L V)) := Fintype.ofFinite _
    simpa only [Nat.card_eq_fintype_card] using (card_le_orbit_quotient_mul_group (L := L) (V := V))
  · exact quotient_stronglyConnected X Quotient.mk'' Quotient.mk''_surjective hsc
  · exact free_quotient_graph_invariant X hX N L act hcompat
  · exact normal_orbit_cycle_lift X hX ht L

end DirectedCycles
