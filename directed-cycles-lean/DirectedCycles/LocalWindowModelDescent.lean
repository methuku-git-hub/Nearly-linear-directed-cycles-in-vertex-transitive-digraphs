import DirectedCycles.LocalWindowQuotientAlgebra

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace EquivalenceWindow
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H} {S W : Set G}
    (C : L.EquivalenceWindow S) (hWS : W ⊆ S)
    (hW1 : L.one ∈ W) (hWi : ∀ x ∈ W, L.inv x ∈ W)
    (hdom : L.AllProductsDefined W 3) (hW3 : L.wordPower W 3 ⊆ S)

def liftHom (f : LocalGroupHom (L.restrict W hW1 hWi) M)
    (hf : ∀ a b : W, C.Rel a.val b.val → f.toFun a = f.toFun b) :
    LocalGroupHom (C.algebra hWS hW1 hWi hdom hW3) M where
  toFun := Quotient.lift f.toFun hf
  map_one := f.map_one
  map_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h x => exact f.map_inv x
  map_mul := by
    rintro _ _ _ ⟨a,b,c,rfl,rfl,rfl,hm⟩
    exact f.map_mul hm

theorem liftHom_image (f : LocalGroupHom (L.restrict W hW1 hWi) M)
    (hf : ∀ a b : W, C.Rel a.val b.val → f.toFun a = f.toFun b) (A : Set W) :
    (C.liftHom hWS hW1 hWi hdom hW3 f hf).toFun '' (C.project hWS '' A) = f.toFun '' A := by
  rw [Set.image_image]
  rfl

/-- A model killing all actual fibre differences is constant on quotient
classes. This uses only its homomorphism laws and local inverse uniqueness. -/
theorem model_constant_of_kills_differences (f : LocalGroupHom L M) {P : Set G}
    (hkill : ∀ p ∈ P, f.toFun p = M.one)
    (hdiff : ∀ a b : W, C.Rel a.val b.val → ∃ p ∈ P, L.mulRel a.val (L.inv b.val) p) :
    ∀ a b : W, C.Rel a.val b.val → f.toFun a.val = f.toFun b.val := by
  intro a b hab
  obtain ⟨p,hp,hm⟩ := hdiff a b hab
  have hh := f.map_mul hm
  rw [f.map_inv,hkill p hp] at hh
  exact (M.inv_injective (M.right_inverse_unique hh)).symm
end EquivalenceWindow
end LocalGroupAlgebra
end DirectedCycles
