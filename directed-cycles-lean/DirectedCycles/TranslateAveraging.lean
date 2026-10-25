module

public import DirectedCycles.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- A translate of any finite sample meets a set in at least its ambient
density. Repeated values of the sample map are counted with multiplicity. -/
theorem dense_translate_sample {G T : Type*} [Group G] [Fintype G] [DecidableEq G]
    (E : Finset G) (S : Finset T) (f : T → G) :
    ∃ z : G, S.card * E.card ≤ Fintype.card G *
      (S.filter (fun t => z * f t ∈ E)).card := by
  classical
  let count : G → ℕ := fun z => (S.filter (fun t => z*f t∈E)).card
  have he : ∑ z : G, count z = S.card * E.card := by
    simp only [count,Finset.card_filter]
    rw [Finset.sum_comm]
    have ht : ∀ t, (∑ z : G, if z*f t ∈ E then 1 else 0) = E.card := by
      intro t
      calc
        _ = ∑ z : G, if z∈E then 1 else 0 :=
          Equiv.sum_comp (Equiv.mulRight (f t)) _
        _ = E.card := by simp
    simp [ht]
  obtain ⟨z,_,hz⟩ := Finset.exists_max_image Finset.univ count Finset.univ_nonempty
  refine ⟨z,?_⟩
  rw [← he]
  calc
    ∑ y : G, count y ≤ ∑ _y : G, count z :=
      Finset.sum_le_sum (fun y hy => hz y hy)
    _ = Fintype.card G * count z := by simp

end DirectedCycles
