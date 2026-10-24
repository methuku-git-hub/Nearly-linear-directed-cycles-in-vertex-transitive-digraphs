import DirectedCycles.ActionBallPaths
import Mathlib.Data.Set.Card

set_option autoImplicit false
namespace DirectedCycles

/-- If a finite reachable ball is stable under one more step, it already
contains every vertex of a strongly connected relation. -/
theorem relationBall_eq_univ_of_stable {V : Type*} (R : Digraph V) (e : V)
    (hconn : StronglyConnected R) (n : ℕ)
    (hstable : relationBall R e (n+1) ⊆ relationBall R e n) :
    relationBall R e n = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  have he : e ∈ relationBall R e n :=
    (relationBall_iff_reachWithin R e e n).mpr (ReachWithin.refl e n)
  have hr := hconn e y
  induction hr with
  | refl => exact he
  | @tail x y _ hxy ih => exact hstable ⟨x,ih,Or.inr hxy⟩

theorem relationBall_card_strict {V : Type*} [Finite V] (R : Digraph V) (e : V)
    (hconn : StronglyConnected R) (n : ℕ) (hn : relationBall R e n ≠ Set.univ) :
    Nat.card (relationBall R e n) < Nat.card (relationBall R e (n+1)) := by
  have hsub : relationBall R e n ⊂ relationBall R e (n+1) := by
    refine ssubset_iff_subset_not_subset.mpr ⟨relationBall_step R e n,?_⟩
    exact fun h => hn (relationBall_eq_univ_of_stable R e hconn n h)
  exact Set.ncard_lt_ncard hsub (Set.toFinite _)

theorem relationBall_card_lower_bound {V : Type*} [Finite V] (R : Digraph V) (e : V)
    (hconn : StronglyConnected R) (n : ℕ) :
    min (n+1) (Nat.card V) ≤ Nat.card (relationBall R e n) := by
  have h : ∀ k, relationBall R e k = Set.univ ∨ k+1 ≤ Nat.card (relationBall R e k) := by
    intro k
    induction k with
    | zero =>
      right
      simpa only [Nat.zero_add,relationBall,Nat.card_coe_set_eq,Set.ncard_singleton] using (show 1 ≤ (1 : ℕ) from le_rfl)
    | succ k ih =>
      by_cases hk : relationBall R e k = Set.univ
      · left
        exact Set.eq_univ_of_univ_subset (hk ▸ relationBall_step R e k)
      · have hh := relationBall_card_strict R e hconn k hk
        exact Or.inr (by have := ih.resolve_left hk; omega)
  rcases h n with hn | hn
  · rw [hn]
    simpa only [Nat.card_coe_set_eq,Set.ncard_univ] using min_le_right (n+1) (Nat.card V)
  · exact (min_le_left _ _).trans hn

end DirectedCycles
