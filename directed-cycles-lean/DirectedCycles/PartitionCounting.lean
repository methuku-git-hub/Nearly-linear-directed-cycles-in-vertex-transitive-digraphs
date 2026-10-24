import DirectedCycles.OrbitRouting

set_option autoImplicit false
namespace DirectedCycles

/-- An equivalence relation with constant class size `m` has exactly
`|V| * (m - 1)` ordered distinct within-class pairs. -/
theorem card_routedPair {V : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → Prop) [DecidableRel E] (hrefl : ∀ x, E x x) (m : ℕ)
    (hm : ∀ x, (Finset.univ.filter (E x)).card = m) :
    Fintype.card (RoutedPair E) = Fintype.card V * (m - 1) := by
  let e : RoutedPair E ≃ Σ x : V, {y // E x y ∧ x ≠ y} := {
    toFun := fun p => ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
    invFun := fun p => ⟨(p.1, p.2.val), p.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  have hx : ∀ x : V, Fintype.card {y // E x y ∧ x ≠ y} = m - 1 := by
    intro x
    rw [Fintype.card_subtype]
    have he : Finset.univ.filter (fun y => E x y ∧ x ≠ y) =
        (Finset.univ.filter (E x)).erase x := by
      ext y
      simp [ne_comm, and_comm]
    rw [he, Finset.card_erase_of_mem (by simp [hrefl x]), hm]
  simp [hx]

/-- Count cut pairs by their common fibre. -/
theorem crossWeight_fibres {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (π : V → W) (S : Finset V) :
    crossWeight (fun x y => π x = π y) S =
      ∑ a : W, ((S.filter (fun x => π x = a)).card : ℝ) *
        ((Sᶜ.filter (fun y => π y = a)).card : ℝ) := by
  classical
  unfold crossWeight cutOut
  rw [← Finset.sum_fiberwise S π (fun x => ∑ y ∈ Sᶜ, if π x = π y then (1 : ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro a _
  have he : ∀ x ∈ S.filter (fun x => π x = a),
      (∑ y ∈ Sᶜ, if π x = π y then (1 : ℝ) else 0) =
      ((Sᶜ.filter (fun y => π y = a)).card : ℝ) := by
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
    simp [eq_comm]
  calc _ = ∑ _x ∈ S.filter (fun x => π x = a),
          ((Sᶜ.filter (fun y => π y = a)).card : ℝ) := Finset.sum_congr rfl he
       _ = _ := by simp

/-- The complement occupies the remaining vertices of a fibre. -/
theorem complement_fibre_card {V W : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq W] (π : V → W) (S : Finset V) (a : W) :
    (Sᶜ.filter (fun x => π x = a)).card =
      (Finset.univ.filter (fun x => π x = a)).card - (S.filter (fun x => π x = a)).card := by
  have he : Sᶜ.filter (fun x => π x = a) =
      (Finset.univ.filter (fun x => π x = a)) \ (S.filter (fun x => π x = a)) := by
    ext x
    simp
    tauto
  rw [he, Finset.card_sdiff_of_subset]
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩

/-- The numerator in manuscript Lemma 4.1 counts one direction of the
within-fibre cut pairs. -/
theorem crossWeight_equal_fibres {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (π : V → W) (S : Finset V) (m : ℕ)
    (hm : ∀ a, (Finset.univ.filter (fun x => π x = a)).card = m) :
    crossWeight (fun x y => π x = π y) S =
      ∑ a : W, ((S.filter (fun x => π x = a)).card : ℝ) *
        (m - ((S.filter (fun x => π x = a)).card : ℝ)) := by
  rw [crossWeight_fibres]
  apply Finset.sum_congr rfl
  intro a _
  rw [complement_fibre_card, hm]
  have hle : (S.filter (fun x => π x = a)).card ≤ m := by
    rw [← hm a]
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  rw [Nat.cast_sub hle]

end DirectedCycles
