import DirectedCycles.FlatMapPositions
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- Ordered list-prefix sums agree with sums over their finite indices. -/
theorem sum_map_take_eq_sum_fin {A : Type*} (xs : List A) (f : A → ℕ) (k : ℕ)
    (hk : k ≤ xs.length) :
    ((xs.take k).map f).sum = ∑ i : Fin k, f (xs[i.val]'(lt_of_lt_of_le i.isLt hk)) := by
  have he : (xs.take k).map f = List.ofFn (fun i : Fin k => f (xs[i.val]'(lt_of_lt_of_le i.isLt hk))) := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_take,List.length_ofFn,Nat.min_eq_left hk]
    · intro j hj hj'
      simp only [List.getElem_map,List.getElem_take,List.getElem_ofFn]
  rw [he,List.sum_ofFn]

/-- Finite blocks in list order are equivalent to positions in their flattened
index interval; the explicit prefix-sum formula is proved below. -/
def listBlockEquiv {A : Type*} (xs : List A) (f : A → ℕ) :
    ((i : Fin xs.length) × Fin (f xs[i.val])) ≃ Fin ((xs.map f).sum) :=
  finSigmaFinEquiv.trans (finCongr (by
    have h := sum_map_take_eq_sum_fin xs f xs.length le_rfl
    simpa only [List.take_length] using h.symm))

theorem listBlockEquiv_val {A : Type*} (xs : List A) (f : A → ℕ)
    (i : Fin xs.length) (j : Fin (f xs[i.val])) :
    (listBlockEquiv xs f ⟨i,j⟩).val = ((xs.take i.val).map f).sum+j.val := by
  simp only [listBlockEquiv,Equiv.trans_apply,finCongr_apply,Fin.val_cast,finSigmaFinEquiv_apply]
  rw [sum_map_take_eq_sum_fin xs f i.val i.isLt.le]
  rfl

end DirectedCycles
