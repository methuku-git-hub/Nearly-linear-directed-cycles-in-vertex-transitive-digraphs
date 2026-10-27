module

public import DirectedCycles.NormalPartitions

@[expose] public section

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- Reachability after forgetting edge directions. -/
def WeakReach {V : Type*} (D : Digraph V) : V → V → Prop :=
  Reachable (fun x y => D x y ∨ D y x)

theorem WeakReach.symm {V : Type*} {D : Digraph V} {x y : V}
    (h : WeakReach D x y) : WeakReach D y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b _ hab ih =>
      have hs : WeakReach D b a := Relation.ReflTransGen.single hab.symm
      exact hs.trans ih

theorem WeakReach.mono {V : Type*} {D E : Digraph V}
    (hDE : ∀ x y, D x y → E x y) {x y : V} (h : WeakReach D x y) :
    WeakReach E x y :=
  reachable_map id (fun _ _ h => h.imp (hDE _ _) (hDE _ _)) h

theorem weakReach_invariant {G V : Type*} [Group G] [MulAction G V]
    (D : Digraph V) (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (g : G) (x y : V) : WeakReach D (g • x) (g • y) ↔ WeakReach D x y := by
  constructor
  · intro h
    have h' := reachable_map (E := fun a b => D a b ∨ D b a) (fun v => g⁻¹ • v)
      (fun a b hab => hab.imp ((hD g⁻¹ a b).mpr) ((hD g⁻¹ b a).mpr)) h
    simpa only [WeakReach, inv_smul_smul] using h'
  · exact reachable_map (fun v => g • v)
      (fun a b hab => hab.imp ((hD g a b).mpr) ((hD g b a).mpr))

/-- The finite vertex set of a weak component. -/
noncomputable def weakComponent {V : Type*} [Fintype V] (D : Digraph V) (x : V) : Finset V :=
  Finset.univ.filter (WeakReach D x)

@[simp] theorem mem_weakComponent {V : Type*} [Fintype V] (D : Digraph V) (x y : V) :
    y ∈ weakComponent D x ↔ WeakReach D x y := by simp [weakComponent]

theorem weakComponent_nonempty {V : Type*} [Fintype V] (D : Digraph V) (x : V) :
    (weakComponent D x).Nonempty := ⟨x, (mem_weakComponent _ _ _).mpr .refl⟩

theorem weakComponent_eq_of_reach {V : Type*} [Fintype V] (D : Digraph V) {x y : V}
    (h : WeakReach D x y) : weakComponent D x = weakComponent D y := by
  ext z
  simp only [mem_weakComponent]
  exact ⟨fun hx => h.symm.trans hx, fun hy => h.trans hy⟩

theorem weakComponent_disjoint {V : Type*} [Fintype V] (D : Digraph V) {x y : V}
    (h : ¬ WeakReach D x y) : Disjoint (weakComponent D x) (weakComponent D y) := by
  rw [Finset.disjoint_left]
  intro z hx hz
  exact h (((mem_weakComponent _ _ _).mp hx).trans
    ((mem_weakComponent _ _ _).mp hz).symm)

theorem weakComponent_card_invariant {G V : Type*} [Group G] [Fintype V] [MulAction G V]
    (D : Digraph V) (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (g : G) (x : V) : (weakComponent D (g • x)).card = (weakComponent D x).card := by
  symm
  apply Finset.card_bijective (MulAction.toPerm g) (MulAction.toPerm g).bijective
  intro y
  simp only [mem_weakComponent]
  exact (weakReach_invariant D hD g x y).symm

theorem weakComponent_eq_univ_iff {V : Type*} [Fintype V] (D : Digraph V) (x : V) :
    weakComponent D x = Finset.univ ↔ Connected D := by
  constructor
  · intro h a b
    have hx : WeakReach D x a := (mem_weakComponent _ _ _).mp (by rw [h]; simp)
    have hy : WeakReach D x b := (mem_weakComponent _ _ _).mp (by rw [h]; simp)
    exact hx.symm.trans hy
  · intro h
    ext y
    simp only [mem_weakComponent, Finset.mem_univ, iff_true]
    exact h x y

theorem stronglyConnected_arc_leaving {V : Type*} [Fintype V]
    (D : Digraph V) (hD : StronglyConnected D) (S : Finset V)
    (hne : S.Nonempty) (hp : S ≠ Finset.univ) :
    ∃ x ∈ S, ∃ y ∉ S, D x y := by
  by_contra hn
  push Not at hn
  obtain ⟨x, hx⟩ := hne
  have hclosed : ∀ y, Reachable D x y → y ∈ S := by
    intro y hy
    induction hy with
    | refl => exact hx
    | tail _ hab ih =>
      by_contra hnot
      exact hn _ ih _ hnot hab
  apply hp
  exact Finset.eq_univ_of_forall (fun y => hclosed y (hD x y))

/-- A new edge to a different old component joins at least two equally sized
components of a transitive invariant graph. -/
theorem weakComponent_doubles {G V : Type*} [Group G] [Fintype V] [MulAction G V]
    (D E : Digraph V) (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (hDE : ∀ x y, D x y → E x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (a b : V)
    (hab : ¬ WeakReach D a b) (he : E a b) :
    2 * (weakComponent D a).card ≤ (weakComponent E a).card := by
  obtain ⟨g, hg⟩ := ht a b
  have hc : (weakComponent D b).card = (weakComponent D a).card := by
    rw [← hg]
    exact weakComponent_card_invariant D hD g a
  have hsub : weakComponent D a ∪ weakComponent D b ⊆ weakComponent E a := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (mem_weakComponent _ _ _).mpr
        (((mem_weakComponent _ _ _).mp hv).mono hDE)
    · apply (mem_weakComponent _ _ _).mpr
      have hs : WeakReach E a b := Relation.ReflTransGen.single (Or.inl he)
      exact hs.trans (((mem_weakComponent _ _ _).mp hv).mono hDE)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (weakComponent_disjoint D hab), hc] at hcard
  omega

end DirectedCycles
