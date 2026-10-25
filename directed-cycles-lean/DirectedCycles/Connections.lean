module

public import DirectedCycles.Basic
public import DirectedCycles.Matching

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The finite closed-set argument used for the orbit connection digraph. -/
theorem permutation_sandwich_stronglyConnected {V : Type*} [Fintype V]
    (D Q : Digraph V) (F : Equiv.Perm V) (hQ : StronglyConnected Q)
    (hskip : ∀ x, Reachable D x (F (F x)))
    (hbridge : ∀ x y, Q (F x) y → Reachable D x (F y)) :
    StronglyConnected D := by
  classical
  intro x y
  let U : Set V := {v | Reachable D x v}
  let F₂ := F.trans F
  have hsub : F₂ '' U ⊆ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact hu.trans (hskip u)
  have heq : F₂ '' U = U := by
    apply Set.eq_of_subset_of_ncard_le hsub
    exact (Set.ncard_image_of_injective U F₂.injective).ge
  let T : Set V := F '' U
  have hclosed : ∀ a ∈ T, ∀ b, Q a b → b ∈ T := by
    intro a ha b hab
    obtain ⟨u, hu, rfl⟩ := ha
    have hb : F b ∈ U := hu.trans (hbridge u b hab)
    rw [← heq] at hb
    obtain ⟨v, hv, he⟩ := hb
    exact ⟨v, hv, F.injective he⟩
  have hreach : ∀ b, Reachable Q (F x) b → b ∈ T := by
    intro b hb
    induction hb with
    | refl => exact ⟨x, Relation.ReflTransGen.refl, rfl⟩
    | tail _ hab ih => exact hclosed _ ih _ hab
  obtain ⟨u, hu, he⟩ := hreach (F y) (hQ _ _)
  have huy := F.injective he
  subst u
  exact hu

/-- `R (identity ∪ Q) R`, with loops removed, as in Lemma 4.2. -/
def ConnectionDigraph {V : Type*} (Q R : Digraph V) : Digraph V :=
  fun x y => x ≠ y ∧ ∃ u v, R x u ∧ (u = v ∨ Q u v) ∧ R v y

theorem connectionDigraph_loopless {V : Type*} (Q R : Digraph V) :
    Loopless (ConnectionDigraph Q R) := fun _x h => h.1 rfl

/-- A matching in `R` suffices for strong connectivity of the sandwich. -/
theorem connectionDigraph_stronglyConnected_of_matching {V : Type*} [Fintype V]
    (Q R : Digraph V) (hQ : StronglyConnected Q)
    (F : Equiv.Perm V) (hF : ∀ x, R x (F x)) :
    StronglyConnected (ConnectionDigraph Q R) := by
  apply permutation_sandwich_stronglyConnected _ Q F hQ
  · intro x
    by_cases hx : x = F (F x)
    · rw [← hx]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨hx, F x, F x, hF x, Or.inl rfl, hF (F x)⟩
  · intro x y hxy
    by_cases hx : x = F y
    · rw [← hx]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨hx, F x, y, hF x, Or.inr hxy, hF y⟩

/-- Transitive invariance supplies the required matching, with no independent
assumption that the connection digraph is strongly connected. -/
theorem connectionDigraph_stronglyConnected {G V : Type*} [Group G] [Fintype V]
    [MulAction G V] (Q R : Digraph V) [DecidableRel R]
    (hQ : StronglyConnected Q) (ht : ∀ x y : V, ∃ g : G, g • x = y)
    (hn : ∃ x y, R x y) (hR : ∀ (g : G) x y, R (g • x) (g • y) ↔ R x y) :
    StronglyConnected (ConnectionDigraph Q R) := by
  obtain ⟨_, _, _, _, F, hF⟩ := symmetry_matching ht ht rfl R hn hR
  exact connectionDigraph_stronglyConnected_of_matching Q R hQ F hF

/-- The connection construction preserves invariance under the group action. -/
theorem connectionDigraph_invariant {G V : Type*} [Group G] [MulAction G V]
    (Q R : Digraph V)
    (hQ : ∀ (g : G) x y, Q (g • x) (g • y) ↔ Q x y)
    (hR : ∀ (g : G) x y, R (g • x) (g • y) ↔ R x y) :
    ∀ (g : G) x y, ConnectionDigraph Q R (g • x) (g • y) ↔ ConnectionDigraph Q R x y := by
  have forward : ∀ (g : G) x y, ConnectionDigraph Q R x y →
      ConnectionDigraph Q R (g • x) (g • y) := by
    intro g x y h
    obtain ⟨hne, u, v, hxu, huv, hvy⟩ := h
    refine ⟨fun he => hne ((MulAction.toPerm g).injective he), g • u, g • v,
      (hR g x u).mpr hxu, ?_, (hR g v y).mpr hvy⟩
    rcases huv with rfl | huv
    · exact Or.inl rfl
    · exact Or.inr ((hQ g u v).mpr huv)
  intro g x y
  constructor
  · intro h
    simpa only [inv_smul_smul] using forward g⁻¹ _ _ h
  · exact forward g x y

end DirectedCycles
