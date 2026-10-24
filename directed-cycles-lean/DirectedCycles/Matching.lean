import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace DirectedCycles
open Finset

/-- The double-counting and Hall step, allowing different vertex types on the sides. -/
theorem regular_bipartite_matching {A B : Type*} [Fintype A] [Fintype B]
    (E : A → B → Prop) [DecidableRel E] (d : ℕ) (hd : 0 < d)
    (hc : Fintype.card A = Fintype.card B)
    (hl : ∀ a, (univ.filter (E a)).card = d)
    (hr : ∀ b, (univ.filter (fun a => E a b)).card = d) :
    ∃ f : A ≃ B, ∀ a, E a (f a) := by
  classical
  let t : A → Finset B := fun a => univ.filter (E a)
  have hall : ∀ s : Finset A, s.card ≤ (s.biUnion t).card := by
    intro s
    let N := s.biUnion t
    have hleft : ∀ a ∈ s, (N.filter (E a)).card = d := by
      intro a ha
      have heq : N.filter (E a) = univ.filter (E a) := by
        ext b
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨mem_biUnion.mpr ⟨a, ha, by simp [t, h]⟩, h⟩⟩
      rw [heq, hl]
    have hright : ∀ b ∈ N, (s.filter (fun a => E a b)).card ≤ d := by
      intro b _
      rw [← hr b]
      exact card_le_card (filter_subset_filter _ (subset_univ s))
    have hcount : s.card * d ≤ N.card * d := by
      exact card_mul_le_card_mul E (fun a ha => (hleft a ha).ge) hright
    exact Nat.le_of_mul_le_mul_right hcount hd
  obtain ⟨f, hf, he⟩ := (all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩
  refine ⟨Equiv.ofBijective f hb, ?_⟩
  intro a
  simpa [t] using he a

/-- Manuscript Lemma 3.1, including the common positive degree and perfect matching.
The two sides are separate types, so the statement also covers equal underlying sets. -/
theorem symmetry_matching {H A B : Type*} [Group H] [Fintype A] [Fintype B]
    [MulAction H A] [MulAction H B]
    (ha : ∀ x x' : A, ∃ g : H, g • x = x')
    (hb : ∀ y y' : B, ∃ g : H, g • y = y')
    (hc : Fintype.card A = Fintype.card B)
    (E : A → B → Prop) [DecidableRel E]
    (hne : ∃ x y, E x y)
    (hinv : ∀ (g : H) x y, E (g • x) (g • y) ↔ E x y) :
    ∃ d : ℕ, 0 < d ∧
      (∀ x, (univ.filter (E x)).card = d) ∧
      (∀ y, (univ.filter (fun x => E x y)).card = d) ∧
      ∃ f : A ≃ B, ∀ x, E x (f x) := by
  classical
  obtain ⟨x₀, y₀, hxy⟩ := hne
  let dA := (univ.filter (E x₀)).card
  let dB := (univ.filter (fun x => E x y₀)).card
  have hl : ∀ x, (univ.filter (E x)).card = dA := by
    intro x
    obtain ⟨g, hg⟩ := ha x x₀
    apply card_bijective (MulAction.toPerm g) (MulAction.toPerm g).bijective
    intro y
    simp only [mem_filter, mem_univ, true_and, MulAction.toPerm_apply]
    rw [← hg]
    exact (hinv g x y).symm
  have hr : ∀ y, (univ.filter (fun x => E x y)).card = dB := by
    intro y
    obtain ⟨g, hg⟩ := hb y y₀
    apply card_bijective (MulAction.toPerm g) (MulAction.toPerm g).bijective
    intro x
    simp only [mem_filter, mem_univ, true_and, MulAction.toPerm_apply]
    rw [← hg]
    exact (hinv g x y).symm
  have hcount : Fintype.card A * dA = Fintype.card B * dB := by
    have h := card_mul_eq_card_mul E (s := (univ : Finset A))
      (t := (univ : Finset B)) (fun a _ => hl a) (fun b _ => hr b)
    simpa using h
  have hn : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨x₀⟩
  have hdeq : dA = dB := by nlinarith [hc]
  have hd : 0 < dA := card_pos.mpr ⟨y₀, by simp [hxy]⟩
  have hr' : ∀ y, (univ.filter (fun x => E x y)).card = dA := by
    intro y
    rw [hr, hdeq]
  exact ⟨dA, hd, hl, hr', regular_bipartite_matching E dA hd hc hl hr'⟩

end DirectedCycles
