module

public import DirectedCycles.CayleyWordTails

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Every vertex of a word walk is its exact ordered prefix product. -/
theorem wordVertices_get {G : Type*} [Group G] (x : G) (xs : List G)
    (i : ℕ) (hi : i < (wordVertices x xs).length) :
    (wordVertices x xs)[i] = x*(xs.take i).prod := by
  induction xs generalizing x i with
  | nil =>
    have hi0 : i = 0 := by simp only [wordVertices_length,List.length_nil] at hi; omega
    subst i
    simp [wordVertices]
  | cons a xs ih =>
    cases i with
    | zero => simp [wordVertices]
    | succ i =>
      simp only [wordVertices,List.getElem_cons_succ,List.take_succ_cons,List.prod_cons]
      rw [ih (x*a) i (by simp only [wordVertices,List.length_cons] at hi; omega)]
      exact mul_assoc x a (xs.take i).prod

/-- An arbitrary relation holds along a word path if it holds for each
explicit prefix step. -/
theorem wordVertices_chain_of_steps {G : Type*} [Group G] (R : Digraph G)
    (x : G) (xs : List G)
    (h : ∀ i : Fin xs.length, R (x*(xs.take i.val).prod) ((x*(xs.take i.val).prod)*xs[i.val])) :
    (wordVertices x xs).IsChain R := by
  apply List.isChain_iff_getElem.mpr
  intro i hi
  have hi' : i < xs.length := by rw [wordVertices_length] at hi; omega
  rw [wordVertices_get,wordVertices_get]
  have he : (xs.take (i+1)).prod = (xs.take i).prod*xs[i] := by
    rw [← List.take_concat_get' xs i hi',List.prod_append,List.prod_singleton]
  rw [he,← mul_assoc]
  exact h ⟨i,hi'⟩

end DirectedCycles
