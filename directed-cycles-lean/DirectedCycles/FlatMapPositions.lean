module

public import DirectedCycles.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A list split at one indexed element, without changing its ordering. -/
theorem list_split_at {A : Type*} (xs : List A) (i : Fin xs.length) :
    xs = xs.take i.val ++ xs[i.val] :: xs.drop (i.val+1) := by
  have h := List.take_append_drop (i.val+1) xs
  rw [← List.take_concat_get' xs i.val i.isLt,List.append_assoc,List.singleton_append] at h
  exact h.symm

/-- Position of one element in a flattened block list. -/
def flatBlockOffset {A B : Type*} (f : A → List B) (xs : List A) (i : Fin xs.length) : ℕ :=
  ((xs.take i.val).flatMap f).length

theorem flatBlock_position_lt {A B : Type*} (f : A → List B) (xs : List A)
    (i : Fin xs.length) (j : ℕ) (hj : j < (f xs[i.val]).length) :
    flatBlockOffset f xs i+j < (xs.flatMap f).length := by
  have h := congrArg (fun ys => (ys.flatMap f).length) (list_split_at xs i)
  simp only [List.flatMap_append,List.flatMap_cons,List.length_append] at h
  dsimp only [flatBlockOffset]
  omega

/-- The flattened prefix is exactly the earlier blocks followed by the chosen
prefix of the current block. -/
theorem flatBlock_take {A B : Type*} (f : A → List B) (xs : List A)
    (i : Fin xs.length) (j : ℕ) (hj : j ≤ (f xs[i.val]).length) :
    (xs.flatMap f).take (flatBlockOffset f xs i+j) =
      (xs.take i.val).flatMap f ++ (f xs[i.val]).take j := by
  have h := congrArg (fun ys => ys.flatMap f) (list_split_at xs i)
  simp only [List.flatMap_append,List.flatMap_cons] at h
  rw [h]
  dsimp only [flatBlockOffset]
  rw [List.take_length_add_append,List.take_append_of_le_length hj]

/-- The chosen flattened entry is the chosen entry within its block. -/
theorem flatBlock_get {A B : Type*} (f : A → List B) (xs : List A)
    (i : Fin xs.length) (j : ℕ) (hj : j < (f xs[i.val]).length) :
    (xs.flatMap f)[flatBlockOffset f xs i+j]'(flatBlock_position_lt f xs i j hj) = (f xs[i.val])[j] := by
  have h := congrArg (fun ys => ys.flatMap f) (list_split_at xs i)
  simp only [List.flatMap_append,List.flatMap_cons] at h
  have ht := congrArg (fun ys => ys[flatBlockOffset f xs i+j]?) h
  dsimp only [flatBlockOffset] at ht
  rw [List.getElem?_append_right (show ((xs.take i.val).flatMap f).length ≤
      ((xs.take i.val).flatMap f).length+j by omega),Nat.add_sub_cancel_left,
    List.getElem?_append_left hj] at ht
  change (xs.flatMap f)[flatBlockOffset f xs i+j]? = (f xs[i.val])[j]? at ht
  rw [List.getElem?_eq_getElem (flatBlock_position_lt f xs i j hj),List.getElem?_eq_getElem hj] at ht
  exact Option.some.inj ht

end DirectedCycles
