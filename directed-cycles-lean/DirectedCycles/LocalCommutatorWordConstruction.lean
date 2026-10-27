module

public import DirectedCycles.LocalCommutatorWordBounds

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A fully defined signed commutator word supplies the actual four-block
commutator product, by compression of all bracketings. -/
theorem commutator_of_signed_word (hr : L.Reversible) {r : ℕ} (g : Fin r → G)
    (w : List (Fin r × Bool)) (j : Fin r) {x z : G}
    (hx : L.Product (L.signedLetters g w) x)
    (hz : L.Product (L.signedLetters g
      (w ++ [(j,true)] ++ inverseSignedWord w ++ [(j,false)])) z) :
    L.Product [x,g j,L.inv x,L.inv (g j)] z := by
  have hiw : L.Product (L.signedLetters g (inverseSignedWord w)) (L.inv x) := by
    rw [L.signedLetters_inverse]
    exact hx.reverse_inv L hr
  have hblocks : List.Forall₂ L.Product
      [L.signedLetters g w,[g j],L.signedLetters g (inverseSignedWord w),[L.inv (g j)]]
      [x,g j,L.inv x,L.inv (g j)] :=
    .cons hx (.cons (.singleton _) (.cons hiw (.cons (.singleton _) .nil)))
  have hflat : L.Product
      [L.signedLetters g w,[g j],L.signedLetters g (inverseSignedWord w),[L.inv (g j)]].flatten z := by
    simpa only [L.signedLetters_append,L.signedLetters_positive_singleton,
      L.signedLetters_negative_singleton,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc] using hz
  exact hflat.compress L hblocks
end LocalGroupAlgebra
end DirectedCycles
