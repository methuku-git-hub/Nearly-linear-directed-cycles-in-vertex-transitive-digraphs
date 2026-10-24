import DirectedCycles.ShortConnections

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- Transitive invariance makes a strict forward majority a strict backward
majority as well, so two bounded walks suffice between any endpoints. -/
theorem short_paths_of_majority {G V : Type*} [Group G] [Fintype V] [DecidableEq V]
    [MulAction G V] (D : Digraph V)
    (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (u : ℕ)
    (hh : ∃ x, Fintype.card V < 2 * (Finset.univ.filter (ReachWithin D u x)).card) :
    ∀ x y, ∃ P : SimplePath D x y, P.length ≤ 2 * u := by
  have hR : ∀ (g : G) x y, ReachWithin D u (g • x) (g • y) ↔ ReachWithin D u x y :=
    fun g x y => reachWithin_invariant D hD g u x y
  obtain ⟨hforward, hback⟩ := invariant_relation_majorities ht ht (Fintype.card V)
    rfl rfl (ReachWithin D u) hR hh
  intro x y
  obtain ⟨z, hz1, hz2⟩ := majority_matching_intersection (Equiv.refl V)
    (Finset.univ.filter (ReachWithin D u x))
    (Finset.univ.filter (fun z => ReachWithin D u z y))
    (Fintype.card V) rfl (hforward x) (hback y)
  have h1 := (Finset.mem_filter.mp hz1).2
  have h2 : ReachWithin D u z y := (Finset.mem_filter.mp hz2).2
  have hpath := reachWithin_iff_simplePath.mp (h1.trans h2)
  simpa only [two_mul] using hpath

/-- With one normal orbit the short-walk majority argument gives prescribed
endpoint connections inside that orbit. This also covers the one-vertex
connection graph used by the sampling method. -/
theorem single_orbit_short_paths {G V : Type*} [Group G] [Fintype G]
    [Fintype V] [DecidableEq V] [MulAction G V] (H : Subgroup G) [H.Normal]
    [Fintype (Quotient (MulAction.orbitRel H V))]
    [DecidableEq (Quotient (MulAction.orbitRel H V))]
    (D : Digraph V) (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (hn : 2 ≤ Fintype.card V)
    (hq : Fintype.card (Quotient (MulAction.orbitRel H V)) = 1)
    (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hdiam : ∀ x y, MulAction.orbitRel H V x y →
      ∃ P : SimplePath (fun u v => D u v ∨ D v u) x y, (P.length : ℝ) ≤ ρ) :
    ∀ x y, ∃ P : SimplePath D x y,
      P.length ≤ 2 * ⌈4 * ρ * Real.log (2 * (Fintype.card V : ℝ))⌉₊ := by
  let Ω := Quotient (MulAction.orbitRel H V)
  let : Subsingleton Ω := Fintype.card_le_one_iff_subsingleton.mp hq.le
  have hsize : ∀ a : Ω, (Finset.univ.filter (fun x : V => Quotient.mk'' x = a)).card = Fintype.card V := by
    intro a
    have he : ∀ x : V, (Quotient.mk'' x : Ω) = a := fun _ => Subsingleton.elim _ _
    simp only [he, Finset.filter_true, Finset.card_univ]
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  obtain ⟨a, ha⟩ := directed_reaches_majority H D hD ht (Fintype.card V) hn ρ hρ hsize hdiam x
  apply short_paths_of_majority D hD ht
  refine ⟨x, ?_⟩
  have hc := Finset.card_le_card (Finset.filter_subset
    (fun y : V => (Quotient.mk'' y : Ω) = a)
    (forwardBall D ⌈4 * ρ * Real.log (2 * (Fintype.card V : ℝ))⌉₊ x))
  exact ha.trans_le (Nat.mul_le_mul_left 2 hc)

end DirectedCycles
