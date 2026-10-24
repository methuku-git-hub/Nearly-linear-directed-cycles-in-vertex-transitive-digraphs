import DirectedCycles.BoundedWalks
import DirectedCycles.Matching

set_option autoImplicit false
namespace DirectedCycles
open scoped Classical

/-- Two strict majorities meet after any bijection between their ambient sets. -/
theorem majority_matching_intersection {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (F : A ≃ B) (S : Finset A) (T : Finset B)
    (m : ℕ) (hB : Fintype.card B = m) (hS : m < 2 * S.card) (hT : m < 2 * T.card) :
    ∃ a ∈ S, F a ∈ T := by
  have hsum : Fintype.card B < (S.map F.toEmbedding).card + T.card := by
    rw [hB, Finset.card_map]
    omega
  obtain ⟨b, hb⟩ := Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.subset_univ (S.map F.toEmbedding)) (Finset.subset_univ T) (by simpa using hsum)
  obtain ⟨a, ha, hab⟩ := Finset.mem_map.mp (Finset.mem_inter.mp hb).1
  exact ⟨a, ha, hab ▸ (Finset.mem_inter.mp hb).2⟩

/-- One heavy row in a transitive invariant bipartite relation makes every
row and every column heavy. -/
theorem invariant_relation_majorities {H A B : Type*} [Group H]
    [Fintype A] [Fintype B] [MulAction H A] [MulAction H B]
    (htA : ∀ x y : A, ∃ g : H, g • x = y)
    (htB : ∀ x y : B, ∃ g : H, g • x = y)
    (m : ℕ) (hA : Fintype.card A = m) (hB : Fintype.card B = m)
    (E : A → B → Prop) [DecidableRel E]
    (hE : ∀ (g : H) a b, E (g • a) (g • b) ↔ E a b)
    (hh : ∃ a, m < 2 * (Finset.univ.filter (E a)).card) :
    (∀ a, m < 2 * (Finset.univ.filter (E a)).card) ∧
    (∀ b, m < 2 * (Finset.univ.filter (fun a => E a b)).card) := by
  obtain ⟨a, ha⟩ := hh
  have hp : 0 < (Finset.univ.filter (E a)).card := by omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hp
  have hne : ∃ a b, E a b := ⟨a, b, (Finset.mem_filter.mp hb).2⟩
  obtain ⟨d, _, hleft, hright, _, _⟩ := symmetry_matching htA htB (hA.trans hB.symm) E hne hE
  have hd : m < 2 * d := by simpa only [hleft a] using ha
  exact ⟨fun a => by rw [hleft]; exact hd, fun b => by rw [hright]; exact hd⟩

/-- Count a predicate in a fibre without changing the underlying vertex count. -/
theorem fibre_filter_card {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (π : V → W) (a : W) (p : V → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun x : {v // π v = a} => p x.val)).card =
      (Finset.univ.filter (fun x => π x = a ∧ p x)).card := by
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property, (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro y hy
    obtain ⟨_, ha, hp⟩ := Finset.mem_filter.mp hy
    exact ⟨⟨y, ha⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩

/-- Majority reachability at both ends, together with a matching between the
intermediate parts, gives a connection of the sum of the three lengths. -/
theorem connection_through_majorities {V A B : Type*} [Fintype A] [Fintype B]
    {D : Digraph V} (f : A → V) (g : B → V) (F : A ≃ B)
    (m u k : ℕ) (hB : Fintype.card B = m) (x y : V)
    (hx : m < 2 * (Finset.univ.filter (fun a => ReachWithin D u x (f a))).card)
    (hy : m < 2 * (Finset.univ.filter (fun b => ReachWithin D u (g b) y)).card)
    (hF : ∀ a, ReachWithin D k (f a) (g (F a))) :
    ReachWithin D (2 * u + k) x y := by
  classical
  obtain ⟨a, ha, hb⟩ := majority_matching_intersection F _ _ m hB hx hy
  have h₁ := (Finset.mem_filter.mp ha).2
  have h₂ := (Finset.mem_filter.mp hb).2
  have h := (h₁.trans (hF a)).trans h₂
  convert h using 1; omega

end DirectedCycles
