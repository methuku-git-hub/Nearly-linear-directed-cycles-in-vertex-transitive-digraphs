import DirectedCycles.CoordinateNormalization

set_option autoImplicit false
namespace DirectedCycles

/-- The baseline labels after passing to baseline-prefix coordinates. -/
def normalizedBaseline {G : Type*} [Group G] (xs : List G) : List G :=
  List.ofFn (fun j : Fin xs.length => coordinateLabel xs j xs[j.val])

@[simp] theorem normalizedBaseline_length {G : Type*} [Group G] (xs : List G) :
    (normalizedBaseline xs).length = xs.length := List.length_ofFn

/-- Every proper normalized prefix is the identity. -/
theorem normalizedBaseline_prefix {G : Type*} [Group G] (xs : List G) (k : ℕ)
    (hk : k < xs.length) : ((normalizedBaseline xs).take k).prod = 1 := by
  apply List.prod_eq_one
  intro a ha
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp ha
  have hjk : j < k := lt_of_lt_of_le hj (List.length_take_le _ _)
  have hjxs : j < xs.length := hjk.trans hk
  rw [List.getElem_take] at he
  simp only [normalizedBaseline,List.getElem_ofFn] at he
  change coordinateLabel xs ⟨j,hjxs⟩ xs[j] = a at he
  have hjnext : j+1 < xs.length := by omega
  have hb : coordinateLabel xs ⟨j,hjxs⟩ xs[j] = 1 := by
    simpa only [Fin.val_mk,hjnext,ite_true] using coordinateLabel_baseline xs ⟨j,hjxs⟩
  exact he.symm.trans hb

/-- The complete normalized baseline product is the original product. -/
theorem normalizedBaseline_prod {G : Type*} [Group G] (xs : List G) (hne : xs ≠ []) :
    (normalizedBaseline xs).prod = xs.prod := by
  have hpos : 0 < xs.length := List.length_pos_iff.mpr hne
  let j : Fin xs.length := ⟨xs.length-1,by omega⟩
  have hj : j.val+1 = xs.length := by dsimp [j]; omega
  have ht : (normalizedBaseline xs).take (j.val+1) = normalizedBaseline xs := by
    rw [hj,← normalizedBaseline_length xs,List.take_length]
  have he := congrArg List.prod (List.take_concat_get' (normalizedBaseline xs) j.val
    (by rw [normalizedBaseline_length]; exact j.isLt))
  rw [ht,List.prod_append,List.prod_singleton,normalizedBaseline_prefix xs j.val j.isLt,one_mul] at he
  simp only [normalizedBaseline,List.getElem_ofFn] at he
  change coordinateLabel xs j xs[j.val] = (normalizedBaseline xs).prod at he
  simp only [coordinateLabel_baseline,hj,lt_self_iff_false,ite_false] at he
  exact he.symm

end DirectedCycles
