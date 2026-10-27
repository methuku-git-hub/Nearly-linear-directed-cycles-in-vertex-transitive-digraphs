module

public import DirectedCycles.NormalOrbits

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The ambient group acts on the orbits of a normal subgroup. No faithfulness
of this induced action is asserted. -/
@[instance_reducible]
def normalOrbitAction {G V : Type*} [Group G] [MulAction G V]
    (H : Subgroup G) [H.Normal] : MulAction G (Quotient (MulAction.orbitRel H V)) where
  smul g := Quotient.map (fun x => g • x) (fun x y h => (normal_orbitRel_invariant H g x y).mpr h)
  one_smul q := by
    induction q using Quotient.inductionOn with
    | _ x => change Quotient.mk'' ((1 : G) • x) = Quotient.mk'' x; simp
  mul_smul g h q := by
    induction q using Quotient.inductionOn with
    | _ x =>
      change Quotient.mk'' ((g * h) • x) = Quotient.mk'' (g • h • x)
      rw [mul_smul]

/-- The normal-orbit projection is equivariant for the induced action. -/
theorem normal_orbit_projection_smul {G V : Type*} [Group G] [MulAction G V]
    (H : Subgroup G) [H.Normal] :
    letI := normalOrbitAction (V := V) H
    ∀ (g : G) x, (Quotient.mk'' (g • x) : Quotient (MulAction.orbitRel H V)) =
      g • (Quotient.mk'' x : Quotient (MulAction.orbitRel H V)) := by
  intro g x
  rfl

theorem equivariant_quotient_transitive {G V W : Type*} [Group G]
    [MulAction G V] [MulAction G W] (π : V → W) (hs : Function.Surjective π)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) :
    ∀ a b : W, ∃ g : G, g • a = b := by
  intro a b
  obtain ⟨x, rfl⟩ := hs a
  obtain ⟨y, rfl⟩ := hs b
  obtain ⟨g, hg⟩ := ht x y
  exact ⟨g, by rw [← hπ, hg]⟩

/-- The fibre map induced by a group element is a bijection. -/
def equivariant_fibre_equiv {G V W : Type*} [Group G]
    [MulAction G V] [MulAction G W] (π : V → W)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) (g : G) (a : W) :
    {x // π x = a} ≃ {x // π x = g • a} :=
  (MulAction.toPerm g).subtypeEquiv (by
    intro x
    change π x = a ↔ π (g • x) = g • a
    rw [hπ]
    exact (MulAction.toPerm g : Equiv.Perm W).injective.eq_iff.symm)

theorem equivariant_equal_fibre_cards {G V W : Type*} [Group G]
    [Fintype V] [DecidableEq W] [MulAction G V] [MulAction G W] (π : V → W)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (ht : ∀ a b : W, ∃ g : G, g • a = b) :
    ∀ a b, Fintype.card {x // π x = a} = Fintype.card {x // π x = b} := by
  intro a b
  obtain ⟨g, rfl⟩ := ht a b
  exact Fintype.card_congr (equivariant_fibre_equiv π hπ g a)

theorem card_eq_quotient_mul_fibre {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq W] (π : V → W) (m : ℕ)
    (hm : ∀ a, Fintype.card {x // π x = a} = m) :
    Fintype.card V = Fintype.card W * m := by
  let e : (Σ a : W, {x // π x = a}) ≃ V := {
    toFun := fun p => p.2.val
    invFun := fun x => ⟨π x, ⟨x, rfl⟩⟩
    left_inv := by rintro ⟨a, x, hx⟩; cases hx; rfl
    right_inv := fun _ => rfl }
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  simp [hm]

/-- Equivariant quotient digraphs inherit the given group symmetry. -/
theorem equivariant_quotient_invariant {G V W : Type*} [Group G]
    [MulAction G V] [MulAction G W] (D : Digraph V) (π : V → W)
    (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) :
    ∀ (g : G) a b, QuotientDigraph D π (g • a) (g • b) ↔ QuotientDigraph D π a b := by
  have forward : ∀ (g : G) a b, QuotientDigraph D π a b →
      QuotientDigraph D π (g • a) (g • b) := by
    intro g a b h
    obtain ⟨hne, x, y, hx, hy, hxy⟩ := h
    refine ⟨fun he => hne ((MulAction.toPerm g).injective he), g • x, g • y, ?_, ?_,
      (hD g x y).mpr hxy⟩
    · rw [hπ, hx]
    · rw [hπ, hy]
  intro g a b
  constructor
  · intro h
    simpa only [inv_smul_smul] using forward g⁻¹ _ _ h
  · exact forward g a b

/-- A transitive automorphism action gives the intrinsic transitivity property. -/
theorem vertexTransitive_of_action {G V : Type*} [Group G] [MulAction G V]
    (D : Digraph V) (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) : VertexTransitive D := by
  intro x y
  obtain ⟨g, hg⟩ := ht x y
  exact ⟨⟨MulAction.toPerm g, hD g⟩, hg⟩

/-- Fibres of the normal-orbit projection are precisely the subgroup orbits,
with transitivity in the direction used by the matching lemmas. -/
theorem normal_orbit_fibre_transitive {G V : Type*} [Group G] [MulAction G V]
    (H : Subgroup G) {x y : V}
    (h : (Quotient.mk'' x : Quotient (MulAction.orbitRel H V)) = Quotient.mk'' y) :
    ∃ g : H, g • x = y := by
  have hrel := Quotient.exact h
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hrel
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

end DirectedCycles
