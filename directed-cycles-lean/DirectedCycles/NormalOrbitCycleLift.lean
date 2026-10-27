module

public import DirectedCycles.CycleLift
public import DirectedCycles.ActionCoordinates
public import DirectedCycles.NormalPartitions

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

theorem normal_orbit_cycle_lift {G V : Type*} [Group G] [Fintype V] [MulAction G V]
    (X : Digraph V) (hX : ∀ g : G, ∀ x y, X (g • x) (g • y) ↔ X x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (L : Subgroup G) [L.Normal]
    (C : Cycle (QuotientDigraph X (Quotient.mk'' : V → Quotient (MulAction.orbitRel L V)))) :
    ∃ D : Cycle X, C.length ≤ D.length := by
  classical
  let Ω := Quotient (MulAction.orbitRel L V)
  let : MulAction G Ω := normalOrbitAction L
  have hπ : ∀ (g : G) x, (Quotient.mk'' (g • x) : Ω) = g • Quotient.mk'' x := fun _ _ => rfl
  have htΩ := equivariant_quotient_transitive (Quotient.mk'' : V → Ω) Quotient.mk''_surjective hπ ht
  apply orbit_cycle_lift (H := L) X (Quotient.mk'' : V → Ω) Quotient.mk''_surjective
    (fun g x => orbitProjection_smul g x) (fun g x y => hX g.val x y) _ _ C
  · intro x y he
    exact MulAction.mem_orbit_iff.mp (Quotient.exact he.symm)
  · intro x y
    simpa only [Nat.card_eq_fintype_card] using
      equivariant_equal_fibre_cards (Quotient.mk'' : V → Ω) hπ htΩ x y

/-- Equivariance is retained when the normal quotient action is subsequently
factored through a subgroup quotient. -/
theorem free_quotient_graph_invariant {G V : Type*} [Group G] [MulAction G V]
    (X : Digraph V) (hX : ∀ g : G, ∀ x y, X (g • x) (g • y) ↔ X x y)
    (N L : Subgroup G) [L.Normal]
    (act : MulAction (N ⧸ L.comap N.subtype) (Quotient (MulAction.orbitRel L V)))
    (hcompat : letI := act
      ∀ (g : N) (x : V), (QuotientGroup.mk g : N ⧸ L.comap N.subtype) • Quotient.mk'' x =
        (Quotient.mk'' (g.val • x) : Quotient (MulAction.orbitRel L V))) :
    letI := act
    ∀ (g : N ⧸ L.comap N.subtype) x y,
      QuotientDigraph X (Quotient.mk'' : V → Quotient (MulAction.orbitRel L V)) (g • x) (g • y) ↔
      QuotientDigraph X (Quotient.mk'' : V → Quotient (MulAction.orbitRel L V)) x y := by
  let : MulAction (N ⧸ L.comap N.subtype) (Quotient (MulAction.orbitRel L V)) := act
  intro g x y
  induction g using Quotient.inductionOn' with
  | h g =>
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
        rw [hcompat,hcompat]
        let : MulAction G (Quotient (MulAction.orbitRel L V)) := normalOrbitAction L
        exact equivariant_quotient_invariant X (Quotient.mk'' : V → Quotient (MulAction.orbitRel L V))
          hX (fun _ _ => rfl) g.val (Quotient.mk'' x) (Quotient.mk'' y)

end DirectedCycles
