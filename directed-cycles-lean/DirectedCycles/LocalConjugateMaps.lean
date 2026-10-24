import DirectedCycles.LocalConjugates
import DirectedCycles.LocalWordPowerMaps

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}

theorem conjugates_image_subset (π : LocalGroupHom L M) (S B : Set G) :
    π.toFun '' (L.conjugates S B) ⊆ M.conjugates (π.toFun '' S) (π.toFun '' B) := by
  rintro x ⟨z,⟨s,hs,b,hb,hp⟩,rfl⟩
  refine ⟨π.toFun s,⟨s,hs,rfl⟩,π.toFun b,⟨b,hb,rfl⟩,?_⟩
  simpa only [List.map_cons,List.map_nil,π.map_inv] using hp.map π

theorem conjugates_mono {S S' B B' : Set G} (hS : S ⊆ S') (hB : B ⊆ B') :
    L.conjugates S B ⊆ L.conjugates S' B' := by
  rintro x ⟨s,hs,b,hb,hp⟩
  exact ⟨s,hS hs,b,hB hb,hp⟩
end LocalGroupAlgebra
end DirectedCycles
