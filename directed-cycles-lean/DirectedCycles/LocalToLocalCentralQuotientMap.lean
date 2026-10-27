module

public import DirectedCycles.LocalCentralQuotientData
public import DirectedCycles.LocalGroupHom

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H} {P : Set G} {Q : Set H}
    (D : L.CentralQuotientData P) (T : M.CentralQuotientData Q)
    (π : LocalGroupHom L M)
    (hPQ : ∀ p ∈ P, π.toFun p ∈ Q) (hDW : ∀ x ∈ D.small, π.toFun x ∈ T.small)

/-- The actual finite-window quotient descends to the actual model quotient.
Class preservation is proved using source relative differences and the local
model homomorphism; neither source globalization nor a global target quotient
by the closure of the curve is assumed. -/
def localModelQuotientMap : D.Carrier → T.Carrier :=
  Quotient.map (fun a : D.small => (⟨π.toFun a.val,hDW a.val a.property⟩ : T.small)) (by
    intro a b hab
    obtain ⟨p,hp,hm⟩ := (D.relation_iff a b).1 hab
    apply (T.relation_iff _ _).2
    refine ⟨π.toFun p,hPQ p hp,?_⟩
    have hh := π.map_mul hm
    simpa only [π.map_inv] using hh)


def localModelQuotientHom : LocalGroupHom D.algebra (T.algebra) where
  toFun := D.localModelQuotientMap T π hPQ hDW
  map_one := by
    change T.project ⟨π.toFun L.one,_⟩ = T.project ⟨M.one,T.one_mem⟩
    congr 1
    exact Subtype.ext π.map_one
  map_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h a =>
      change T.project ⟨π.toFun (L.inv a.val),_⟩ =
        T.project ⟨M.inv (π.toFun a.val),_⟩
      congr 1
      exact Subtype.ext (π.map_inv a.val)
  map_mul := by
    rintro x y z ⟨a,b,c,ha,hb,hc,hab⟩
    refine ⟨⟨π.toFun a.val,hDW a.val a.property⟩,⟨π.toFun b.val,hDW b.val b.property⟩,
      ⟨π.toFun c.val,hDW c.val c.property⟩,?_,?_,?_,π.map_mul hab⟩
    · exact congrArg (D.localModelQuotientMap T π hPQ hDW) ha
    · exact congrArg (D.localModelQuotientMap T π hPQ hDW) hb
    · exact congrArg (D.localModelQuotientMap T π hPQ hDW) hc

theorem localModelQuotientHom_projection (a : D.small) :
    (D.localModelQuotientHom T π hPQ hDW).toFun (D.project a) =
      T.project ⟨π.toFun a.val,hDW a.val a.property⟩ := rfl

/-- The target local central quotient kills precisely its specified central
set, on its actual small window. -/
theorem project_eq_one_iff (a : D.small) : D.project a = D.algebra.one ↔ a.val ∈ P := by
  change D.project a = D.project ⟨L.one,D.one_mem⟩ ↔ _
  rw [D.project_eq_iff,D.relation_iff]
  constructor
  · rintro ⟨p,hp,hm⟩
    rw [L.inv_one] at hm
    exact (L.unique hm (L.mul_one a.val)) ▸ hp
  · intro ha
    exact ⟨a.val,ha,by rw [L.inv_one]; exact L.mul_one a.val⟩

theorem localModelQuotientHom_kernel (a : D.small) :
    (D.localModelQuotientHom T π hPQ hDW).toFun (D.project a) = T.algebra.one ↔ π.toFun a.val ∈ Q := by
  rw [D.localModelQuotientHom_projection]
  exact T.project_eq_one_iff _

theorem localModelQuotientHom_image (B : Set D.small) :
    (D.localModelQuotientHom T π hPQ hDW).toFun '' (D.project '' B) =
      T.project '' ((fun a : D.small => (⟨π.toFun a.val,hDW a.val a.property⟩ : T.small)) '' B) := by
  rw [Set.image_image,Set.image_image]
  rfl

theorem localModelQuotientHom_surjective
    (hsurj : ∀ y ∈ T.small, ∃ x ∈ D.small, π.toFun x = y) :
    Function.Surjective (D.localModelQuotientHom T π hPQ hDW).toFun := by
  intro y
  induction y using Quotient.inductionOn with
  | h b =>
    obtain ⟨a,ha,hab⟩ := hsurj b.val b.property
    refine ⟨D.project ⟨a,ha⟩,?_⟩
    rw [D.localModelQuotientHom_projection]
    congr 1
    exact Subtype.ext hab
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
