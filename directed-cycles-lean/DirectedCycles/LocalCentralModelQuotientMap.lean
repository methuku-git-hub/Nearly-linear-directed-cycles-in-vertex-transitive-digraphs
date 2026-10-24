import DirectedCycles.LocalCentralQuotientData
import DirectedCycles.LocalQuotientHom

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G H : Type*} {L : LocalGroupAlgebra G} [Group H] {P : Set G}
    (D : L.CentralQuotientData P) {Q V W : Set H} (hQ : LocalNormalSet Q V)
    (hW1 : (1 : H) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)
    (π : LocalGroupHom L (LocalGroupAlgebra.ofGroup H))
    (hPQ : ∀ p ∈ P, π.toFun p ∈ Q) (hDW : ∀ x ∈ D.small, π.toFun x ∈ W)

/-- The actual finite-window quotient descends to the actual model quotient.
Class preservation is proved using source relative differences and the local
model homomorphism; neither source globalization nor a global target quotient
by the closure of the curve is assumed. -/
def modelQuotientMap : D.Carrier → hQ.WindowQuotient hW1 hWi hW6 :=
  Quotient.map (fun a : D.small => (⟨π.toFun a.val,hDW a.val a.property⟩ : W)) (by
    intro a b hab
    obtain ⟨p,hp,hm⟩ := (D.relation_iff a b).1 hab
    change π.toFun a.val*(π.toFun b.val)⁻¹ ∈ Q
    have he := π.map_mul hm
    change π.toFun a.val*π.toFun (L.inv b.val) = π.toFun p at he
    rw [π.map_inv] at he
    change π.toFun a.val*(π.toFun b.val)⁻¹ = π.toFun p at he
    rw [he]
    exact hPQ p hp)

def modelQuotientHom : LocalGroupHom D.algebra (hQ.quotientAlgebra hW1 hWi hW6) where
  toFun := D.modelQuotientMap hQ hW1 hWi hW6 π hPQ hDW
  map_one := by
    change hQ.windowMk hW1 hWi hW6 ⟨π.toFun L.one,_⟩ = hQ.windowMk hW1 hWi hW6 ⟨1,hW1⟩
    congr 1
    exact Subtype.ext π.map_one
  map_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h a =>
      change hQ.windowMk hW1 hWi hW6 ⟨π.toFun (L.inv a.val),_⟩ =
        hQ.windowMk hW1 hWi hW6 ⟨(π.toFun a.val)⁻¹,_⟩
      congr 1
      exact Subtype.ext (π.map_inv a.val)
  map_mul := by
    rintro x y z ⟨a,b,c,ha,hb,hc,hab⟩
    refine ⟨⟨π.toFun a.val,hDW a.val a.property⟩,⟨π.toFun b.val,hDW b.val b.property⟩,
      ⟨π.toFun c.val,hDW c.val c.property⟩,?_,?_,?_,π.map_mul hab⟩
    · exact congrArg (D.modelQuotientMap hQ hW1 hWi hW6 π hPQ hDW) ha
    · exact congrArg (D.modelQuotientMap hQ hW1 hWi hW6 π hPQ hDW) hb
    · exact congrArg (D.modelQuotientMap hQ hW1 hWi hW6 π hPQ hDW) hc

theorem modelQuotientHom_projection (a : D.small) :
    (D.modelQuotientHom hQ hW1 hWi hW6 π hPQ hDW).toFun (D.project a) =
      hQ.windowMk hW1 hWi hW6 ⟨π.toFun a.val,hDW a.val a.property⟩ := rfl

theorem modelQuotientHom_kernel (a : D.small) :
    (D.modelQuotientHom hQ hW1 hWi hW6 π hPQ hDW).toFun (D.project a) =
      (hQ.quotientAlgebra hW1 hWi hW6).one ↔ π.toFun a.val ∈ Q := by
  rw [D.modelQuotientHom_projection]
  change hQ.windowMk hW1 hWi hW6 ⟨π.toFun a.val,_⟩ = hQ.windowMk hW1 hWi hW6 ⟨1,hW1⟩ ↔ _
  rw [LocalNormalSet.window_quotient_eq_iff]
  simp

theorem modelQuotientHom_image (B : Set D.small) :
    (D.modelQuotientHom hQ hW1 hWi hW6 π hPQ hDW).toFun '' (D.project '' B) =
      hQ.windowMk hW1 hWi hW6 '' ((fun a : D.small => (⟨π.toFun a.val,hDW a.val a.property⟩ : W)) '' B) := by
  rw [Set.image_image,Set.image_image]
  rfl

theorem modelQuotientHom_surjective
    (hsurj : ∀ y ∈ W, ∃ x ∈ D.small, π.toFun x = y) :
    Function.Surjective (D.modelQuotientHom hQ hW1 hWi hW6 π hPQ hDW).toFun := by
  intro y
  induction y using Quotient.inductionOn with
  | h b =>
    obtain ⟨a,ha,hab⟩ := hsurj b.val b.property
    refine ⟨D.project ⟨a,ha⟩,?_⟩
    rw [D.modelQuotientHom_projection]
    congr 1
    exact Subtype.ext hab
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
