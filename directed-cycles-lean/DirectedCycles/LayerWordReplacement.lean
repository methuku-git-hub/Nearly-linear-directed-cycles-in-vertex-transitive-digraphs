module

public import DirectedCycles.CyclicLayerRounds

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Allowed words are characterized by their indexed labels. -/
theorem layerWord_iff_get {G : Type*} [Group G] {T : ℕ}
    (S : ZMod T → Set G) (i : ZMod T) (xs : List G) :
    LayerWord S i xs ↔ ∀ j : Fin xs.length, xs[j.val] ∈ S (i+j.val) := by
  induction xs generalizing i with
  | nil => simp [LayerWord]
  | cons a xs ih =>
    rw [LayerWord,ih]
    constructor
    · rintro ⟨ha,hxs⟩ j
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa using ha
      · simpa only [Fin.val_succ,List.getElem_cons_succ,Nat.cast_add,Nat.cast_one,
          add_assoc,add_comm,add_left_comm] using hxs k
    · intro h
      refine ⟨?_,?_⟩
      · simpa using h 0
      · intro j
        simpa only [Fin.val_succ,List.getElem_cons_succ,Nat.cast_add,Nat.cast_one,
          add_assoc,add_comm,add_left_comm] using h j.succ

/-- Replacing one label by another allowed at the same position preserves the word. -/
theorem layerWord_set {G : Type*} [Group G] {T : ℕ}
    (S : ZMod T → Set G) (i : ZMod T) (xs : List G) (hxs : LayerWord S i xs)
    (j : ℕ) (a : G) (ha : a ∈ S (i+j)) : LayerWord S i (xs.set j a) := by
  apply (layerWord_iff_get S i _).mpr
  intro k
  have hk : k.val < xs.length := by simpa using k.isLt
  by_cases he : k.val = j
  · simpa only [List.getElem_set,he.symm,ite_true] using ha
  · have h := (layerWord_iff_get S i xs).mp hxs ⟨k.val,hk⟩
    simpa only [List.getElem_set,Ne.symm he,ite_false] using h

/-- Replacing one entry changes an ordered product by its prefix-conjugated
relative label. No commutativity is used. -/
theorem list_product_replacement {G : Type*} [Group G] (xs : List G)
    (j : ℕ) (hj : j < xs.length) (a : G) :
    (xs.set j a).prod = (xs.take j).prod * a * (xs[j])⁻¹ *
      ((xs.take j).prod)⁻¹ * xs.prod := by
  have hsprod : xs.prod = (xs.take j).prod * xs[j] * (xs.drop (j+1)).prod := by
    have h := congrArg List.prod (List.take_append_drop (j+1) xs)
    rw [← List.take_concat_get' xs j hj,List.prod_append,List.prod_append,List.prod_singleton] at h
    exact h.symm
  simp only [List.prod_set,hj,ite_true]
  rw [hsprod]
  group

end DirectedCycles
