module

public import DirectedCycles.CosetNilprogression

@[expose] public section

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- Actual signed words commute with group homomorphisms. -/
theorem map_signedWordValue {G H : Type*} [Group G] [Group H] {r : ℕ}
    (f : G →* H) (g : Fin r → G) (w : List (Fin r × Bool)) :
    f (signedWordValue g w) = signedWordValue (fun i => f (g i)) w := by
  induction w with
  | nil => exact map_one f
  | cons a w ih =>
    simp only [signedWordValue,List.map_cons,List.prod_cons] at ih ⊢
    rw [map_mul,ih]
    congr 1
    split
    · rfl
    · exact map_inv f _

/-- Every binary generator commutator is preserved, with its exact word. -/
theorem CommutatorWord.map_eval {G H α : Type*} [Group G] [Group H]
    (f : G →* H) (g : α → G) (w : CommutatorWord α) :
    f (w.eval g) = w.eval (fun i => f (g i)) := by
  induction w with
  | var _ => rfl
  | bracket a b ha hb =>
    simp only [CommutatorWord.eval,map_commutatorElement,ha,hb]
end DirectedCycles
