import DirectedCycles.HeavyReach
import DirectedCycles.Connections

set_option autoImplicit false
namespace DirectedCycles
open scoped Classical

/-- The sandwich relation connects arbitrary endpoints within the announced
length once its heavy relations have heavy rows and columns. -/
theorem connectionDigraph_short_paths {V W : Type*} [Fintype V] [DecidableEq W]
    (D : Digraph V) (π : V → W) (u m : ℕ)
    (hsize : ∀ a, Fintype.card {x // π x = a} = m)
    (hmajor : ∀ a b, HeavyReach D π u m a b →
      (∀ x : {v // π v = a}, m < 2 *
        (Finset.univ.filter (fun y : {v // π v = b} => ReachWithin D u x.val y.val)).card) ∧
      (∀ y : {v // π v = b}, m < 2 *
        (Finset.univ.filter (fun x : {v // π v = a} => ReachWithin D u x.val y.val)).card))
    (hmatch : ∀ a b, QuotientDigraph D π a b →
      ∃ F : {x // π x = a} ≃ {x // π x = b}, ∀ x, D x.val (F x).val) :
    ∀ a b, ConnectionDigraph (QuotientDigraph D π) (HeavyReach D π u m) a b →
      ∀ (x : {v // π v = a}) (y : {v // π v = b}),
        ∃ P : SimplePath D x.val y.val, P.length ≤ 2 * u + 1 := by
  intro a b hab x y
  obtain ⟨_, c, d, hac, hcd, hdb⟩ := hab
  have hx := (hmajor a c hac).1 x
  have hy := (hmajor d b hdb).2 y
  apply reachWithin_iff_simplePath.mp
  rcases hcd with rfl | hcd
  · exact connection_through_majorities Subtype.val Subtype.val (Equiv.refl {v // π v = c})
      m u 1 (hsize c) x.val y.val hx hy (fun z => ReachWithin.refl z.val 1)
  · obtain ⟨F, hF⟩ := hmatch c d hcd
    exact connection_through_majorities Subtype.val Subtype.val F m u 1 (hsize d)
      x.val y.val hx hy (fun z => ReachWithin.arc (hF z))

/-- Assemble the invariant strongly connected connection digraph from the
routing and symmetry conclusions, retaining the prescribed-endpoint bound. -/
theorem short_connections_from_heavy {G V W : Type*} [Group G]
    [Fintype V] [Fintype W] [DecidableEq W] [MulAction G W]
    (D : Digraph V) (π : V → W) (u m : ℕ)
    (hsize : ∀ a, Fintype.card {x // π x = a} = m)
    (hQ : StronglyConnected (QuotientDigraph D π))
    (ht : ∀ a b : W, ∃ g : G, g • a = b)
    (hQi : ∀ (g : G) a b, QuotientDigraph D π (g • a) (g • b) ↔ QuotientDigraph D π a b)
    (hRi : ∀ (g : G) a b, HeavyReach D π u m (g • a) (g • b) ↔ HeavyReach D π u m a b)
    (hne : ∃ a b, HeavyReach D π u m a b)
    (hmajor : ∀ a b, HeavyReach D π u m a b →
      (∀ x : {v // π v = a}, m < 2 *
        (Finset.univ.filter (fun y : {v // π v = b} => ReachWithin D u x.val y.val)).card) ∧
      (∀ y : {v // π v = b}, m < 2 *
        (Finset.univ.filter (fun x : {v // π v = a} => ReachWithin D u x.val y.val)).card))
    (hmatch : ∀ a b, QuotientDigraph D π a b →
      ∃ F : {x // π x = a} ≃ {x // π x = b}, ∀ x, D x.val (F x).val) :
    ∃ Q : Digraph W, Loopless Q ∧ StronglyConnected Q ∧
      (∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b) ∧
      ∀ a b, Q a b → ∀ (x : {v // π v = a}) (y : {v // π v = b}),
        ∃ P : SimplePath D x.val y.val, P.length ≤ 2 * u + 1 := by
  exact ⟨ConnectionDigraph (QuotientDigraph D π) (HeavyReach D π u m),
    connectionDigraph_loopless _ _, connectionDigraph_stronglyConnected _ _ hQ ht hne hRi,
    connectionDigraph_invariant _ _ hQi hRi,
    connectionDigraph_short_paths D π u m hsize hmajor hmatch⟩

/-- Manuscript Lemma 4.2, with the normal-orbit action and the connection-length
bound explicit. Uniform orbit size is derived from ambient transitivity. -/
theorem short_directed_connections {G V : Type*} [Group G] [Fintype G]
    [Fintype V] [DecidableEq V] [MulAction G V]
    (H : Subgroup G) [H.Normal]
    [Fintype (Quotient (MulAction.orbitRel H V))]
    [DecidableEq (Quotient (MulAction.orbitRel H V))]
    (D : Digraph V) (hconnected : Connected D)
    (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y)
    (hq : 2 ≤ Fintype.card (Quotient (MulAction.orbitRel H V)))
    (hsize : ∀ a : Quotient (MulAction.orbitRel H V),
      2 ≤ Fintype.card {x : V // Quotient.mk'' x = a})
    (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hdiam : ∀ x y, MulAction.orbitRel H V x y →
      ∃ P : SimplePath (fun u v => D u v ∨ D v u) x y, (P.length : ℝ) ≤ ρ) :
    letI := normalOrbitAction (V := V) H
    ∃ Q : Digraph (Quotient (MulAction.orbitRel H V)), Loopless Q ∧ StronglyConnected Q ∧
      (∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b) ∧
      ∀ a b, Q a b → ∀ (x : {v : V // Quotient.mk'' v = a}) (y : {v : V // Quotient.mk'' v = b}),
        ∃ P : SimplePath D x.val y.val,
          P.length ≤ 2 * ⌈4 * ρ * Real.log (2 * (Fintype.card V : ℝ))⌉₊ + 1 := by
  let Ω := Quotient (MulAction.orbitRel H V)
  let π : V → Ω := Quotient.mk''
  let : MulAction G Ω := normalOrbitAction H
  let u := ⌈4 * ρ * Real.log (2 * (Fintype.card V : ℝ))⌉₊
  have hs : Function.Surjective π := Quotient.mk''_surjective
  have hπ : ∀ (g : G) x, π (g • x) = g • π x := normal_orbit_projection_smul H
  have htΩ := equivariant_quotient_transitive π hs hπ ht
  have hequal := equivariant_equal_fibre_cards π hπ htΩ
  have hΩpos : 0 < Fintype.card Ω := lt_of_lt_of_le (by decide : 0 < 2) hq
  let : Nonempty Ω := Fintype.card_pos_iff.mp hΩpos
  let a₀ : Ω := Classical.choice inferInstance
  let m := Fintype.card {x // π x = a₀}
  have hm : 2 ≤ m := hsize a₀
  have hmcard : ∀ a, Fintype.card {x // π x = a} = m := fun a => hequal a a₀
  have hmfilter : ∀ a : Ω, (Finset.univ.filter (fun x => π x = a)).card = m := by
    intro a
    simpa only [Fintype.card_subtype] using hmcard a
  have hstrong : StronglyConnected D :=
    (vertexTransitive_connected_iff_stronglyConnected (vertexTransitive_of_action D hD ht)).mp hconnected
  have hQ := quotient_stronglyConnected D π hs hstrong
  have hQi := equivariant_quotient_invariant D π hD hπ
  have hRi := heavyReach_invariant D π hπ hD u m
  have hne : ∃ a b, HeavyReach D π u m a b := by
    obtain ⟨x, hx⟩ := hs a₀
    obtain ⟨b, hb⟩ := directed_reaches_majority H D hD ht m hm ρ hρ hmfilter hdiam x
    refine ⟨a₀, b, ⟨x, hx⟩, ?_⟩
    rw [fibre_filter_card π b (fun y => ReachWithin D u x y)]
    simpa only [forwardBall, Finset.filter_filter, and_comm] using hb
  have hHπ : ∀ (g : H) x, π (g • x) = π x := by
    intro g x
    apply Quotient.sound
    exact MulAction.mem_orbit x g
  have hHD : ∀ (g : H) x y, D (g • x) (g • y) ↔ D x y := fun g x y => hD g.val x y
  have hHtrans : ∀ x y, π x = π y → ∃ g : H, g • x = y :=
    fun _ _ h => normal_orbit_fibre_transitive H h
  exact short_connections_from_heavy D π u m hmcard hQ htΩ hQi hRi hne
    (fun _ _ h => heavyReach_majorities D π hHπ hHD hHtrans u m hmcard h)
    (fun _ _ h => orbit_arc_matching D π hHπ hHD hHtrans hequal h)

end DirectedCycles
