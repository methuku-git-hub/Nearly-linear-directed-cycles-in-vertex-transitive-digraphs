import DirectedCycles.LocalProgressionWitness

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}

/-- An actual local homomorphism transports every signed word in a bounded
coordinate box. -/
theorem SignedWordsIn.image {r : ℕ} {g : Fin r → G} {N : Fin r → ℕ} {A : Set G}
    (h : L.SignedWordsIn g N A) (f : LocalGroupHom L M) :
    M.SignedWordsIn (fun i => f.toFun (g i)) N (f.toFun '' A) := by
  intro w hw
  obtain ⟨x,hx,hp⟩ := h w hw
  refine ⟨f.toFun x,⟨x,hx,rfl⟩,?_⟩
  simpa only [f.map_signedLetters] using hp.map f

/-- The actual ordered grid commutes with a local homomorphism. -/
theorem orderedGrid_image {r : ℕ} {g : Fin r → G} {N : Fin r → ℕ} {A : Set G}
    (h : L.SignedWordsIn g N A) (f : LocalGroupHom L M) (k : SignedCoordinates N) :
    f.toFun (L.orderedGrid h k).val = (M.orderedGrid (h.image f) k).val := by
  have hp := (L.orderedGrid_product h k).map f
  change M.Product ((L.signedLetters g (orderedSignedWord (fun i => (k i).val))).map f.toFun)
    (f.toFun (L.orderedGrid h k).val) at hp
  rw [f.map_signedLetters] at hp
  exact hp.unique M (M.orderedGrid_product (h.image f) k)

 theorem orderedGrid_image_injective {r : ℕ} {g : Fin r → G} {N : Fin r → ℕ} {A : Set G}
    (h : L.SignedWordsIn g N A) (f : LocalGroupHom L M) (hf : Function.Injective f.toFun)
    (hp : Function.Injective (L.orderedGrid h)) :
    Function.Injective (M.orderedGrid (h.image f)) := by
  intro k l he
  apply hp
  apply Subtype.ext
  apply hf
  rw [orderedGrid_image h f k,orderedGrid_image h f l]
  exact congrArg Subtype.val he
end LocalGroupAlgebra
end DirectedCycles
