module

public import DirectedCycles.LocalGroupUltraproduct
public import Mathlib.Data.List.OfFn

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A component family of lists of one fixed length is an actual list of
dependent representatives, with exact evaluation in every component. -/
theorem exists_uniform_list_representatives {ι : Type*} (G : ι → Type*)
    (l : ∀ i, List (G i)) {n : ℕ} (hlen : ∀ i, (l i).length = n) :
    ∃ a : List (∀ i, G i), a.length = n ∧ ∀ i, a.map (fun v => v i) = l i := by
  let a : List (∀ i, G i) := List.ofFn (fun j : Fin n => fun i => (l i)[j.val]'(by rw [hlen i]; exact j.isLt))
  refine ⟨a,by simp [a],?_⟩
  intro i
  apply List.ext_getElem
  · simp only [List.length_map,a,List.length_ofFn,hlen i]
  · intro j hj hj'
    simp only [List.getElem_map,a,List.getElem_ofFn]

theorem exists_localUltra_list_representatives {ι : Type*} (F : Filter ι) (G : ι → Type*)
    (l : List (LocalUltraproduct F G)) :
    ∃ a : List (∀ i, G i), a.map (localUltraMk F G) = l := by
  induction l with
  | nil => exact ⟨[],rfl⟩
  | cons x l ih =>
    obtain ⟨v,rfl⟩ := Quotient.exists_rep x
    obtain ⟨a,ha⟩ := ih
    exact ⟨v::a,by simp only [List.map_cons,ha]⟩
end DirectedCycles
