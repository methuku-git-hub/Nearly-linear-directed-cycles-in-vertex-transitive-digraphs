import DirectedCycles.LocalSignedWords
import DirectedCycles.LocalProductInversion

set_option autoImplicit false
namespace DirectedCycles

def inverseSignedWord {r : ℕ} (w : List (Fin r × Bool)) : List (Fin r × Bool) :=
  w.reverse.map (fun a => (a.1,!a.2))

@[simp] theorem inverseSignedWord_length {r : ℕ} (w : List (Fin r × Bool)) :
    (inverseSignedWord w).length = w.length := by simp [inverseSignedWord]

namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem signedLetters_inverse {r : ℕ} (g : Fin r → G) (w : List (Fin r × Bool)) :
    L.signedLetters g (inverseSignedWord w) = (L.signedLetters g w).reverse.map L.inv := by
  simp only [signedLetters,inverseSignedWord,List.map_map,List.map_reverse]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro a _
  cases a with
  | mk i b => cases b <;> simp [L.inv_inv]

theorem signedLetters_append {r : ℕ} (g : Fin r → G) (a b : List (Fin r × Bool)) :
    L.signedLetters g (a++b) = L.signedLetters g a ++ L.signedLetters g b := List.map_append

theorem signedLetters_positive_singleton {r : ℕ} (g : Fin r → G) (i : Fin r) :
    L.signedLetters g [(i,true)] = [g i] := rfl

theorem signedLetters_negative_singleton {r : ℕ} (g : Fin r → G) (i : Fin r) :
    L.signedLetters g [(i,false)] = [L.inv (g i)] := rfl
end LocalGroupAlgebra
end DirectedCycles
