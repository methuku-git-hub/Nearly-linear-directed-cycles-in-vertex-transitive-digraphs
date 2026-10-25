module

public import DirectedCycles.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Greedy assignment for reciprocal pairwise forbidden sets. The bound is
uniform over choices already made, so every condition is checked when its
second variable is assigned. Self-pairs are excluded explicitly. -/
theorem finite_forbidden_assignment {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I]
    [Nonempty A] (bad : I → I → A → Finset A)
    (hsym : ∀ i j a b, a ∈ bad i j b ↔ b ∈ bad j i a)
    (hbound : ∀ i (f : I → A), (∑ j ∈ Finset.univ.erase i, (bad i j (f j)).card) < Fintype.card A) :
    ∃ f : I → A, ∀ i j, i ≠ j → f i ∉ bad i j (f j) := by
  classical
  have hpartial : ∀ s : Finset I, ∃ f : I → A,
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i ∉ bad i j (f j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => Classical.choice (inferInstance : Nonempty A),by simp⟩
    | @insert i s hi ih =>
      obtain ⟨f,hf⟩ := ih
      let F := s.biUnion (fun j => bad i j (f j))
      have hcard : F.card < Fintype.card A := by
        have hs : s ⊆ Finset.univ.erase i := by
          intro j hj
          exact Finset.mem_erase.mpr ⟨fun he => hi (he ▸ hj),Finset.mem_univ _⟩
        exact (Finset.card_biUnion_le).trans_lt
          ((Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)).trans_lt (hbound i f))
      obtain ⟨a,ha⟩ : ∃ a : A, a ∉ F := by
        by_contra he
        push Not at he
        have hF : F = Finset.univ := Finset.eq_univ_of_forall he
        rw [hF,Finset.card_univ] at hcard
        exact (lt_irrefl _ hcard)
      let g := Function.update f i a
      have hgi : g i = a := by simp only [g,Function.update_self]
      have hgj : ∀ j ∈ s, g j = f j := by
        intro j hj
        exact Function.update_of_ne (show j ≠ i from fun he => hi (he ▸ hj)) _ _
      have hnew : ∀ j ∈ s, a ∉ bad i j (f j) := by
        intro j hj hb
        exact ha (Finset.mem_biUnion.mpr ⟨j,hj,hb⟩)
      refine ⟨g,?_⟩
      intro j hj l hl hjl
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        have hls : l ∈ s := (Finset.mem_insert.mp hl).resolve_left (Ne.symm hjl)
        rw [hgi,hgj l hls]
        exact hnew l hls
      · rcases Finset.mem_insert.mp hl with hli | hls
        · subst l
          rw [hgi,hgj j hjs]
          exact fun hh => hnew j hjs ((hsym i j a (f j)).mpr hh)
        · rw [hgj j hjs,hgj l hls]
          exact hf j hjs l hls hjl
  obtain ⟨f,hf⟩ := hpartial Finset.univ
  exact ⟨f,fun i j hij => hf i (Finset.mem_univ i) j (Finset.mem_univ j) hij⟩

end DirectedCycles
