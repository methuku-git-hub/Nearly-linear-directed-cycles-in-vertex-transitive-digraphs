module

public import DirectedCycles.LocalToLocalCentralQuotientMap
public import DirectedCycles.LocalDivision

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}
    {P : Set G} {Q : Set H} (D : L.CentralQuotientData P) (T : M.CentralQuotientData Q)

/-- Small and thick neighbourhoods descend to the actual central quotient.
A target central difference is lifted through the exact progression image;
an actual source correction then enters the inner source neighbourhood. -/
theorem localModelQuotientHom_neighbourhood (hd : L.DivisionClosed) (hM : M.DivisionClosed)
    (π : LocalGroupHom L M)
    (hPQ : ∀ p ∈ P, π.toFun p ∈ Q) (hDW : ∀ x ∈ D.small, π.toFun x ∈ T.small)
    (hQP : Q ⊆ π.toFun '' P) (hPi : ∀ p ∈ P, L.inv p ∈ P)
    (A B : Set G) (hPA : P ⊆ A) (hDA : D.small ⊆ A)
    (hAi : ∀ x ∈ A, L.inv x ∈ A) (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y)
    (hBD : B ⊆ D.small) (V : Set H)
    (hsmall : ∀ x, π.toFun x ∈ V → x ∈ B)
    (hthick : ∀ v ∈ V, ∃ x, π.toFun x = v) :
    let Vq := T.project '' {v : T.small | v.val ∈ V}
    (D.localModelQuotientHom T π hPQ hDW).toFun ⁻¹' Vq ⊆
      D.project '' {x : D.small | x.val ∈ B} ∧
    Vq ⊆ (D.localModelQuotientHom T π hPQ hDW).toFun ''
      (D.project '' {x : D.small | x.val ∈ B}) := by
  intro Vq
  constructor
  · intro y hy
    induction y using Quotient.inductionOn with
    | h a =>
      obtain ⟨v,hv,he⟩ := hy
      have he' : T.project ⟨π.toFun a.val,hDW a.val a.property⟩ =
          T.project v := he.symm
      obtain ⟨q,hq,hqrel⟩ := (T.relation_iff _ _).1 ((T.project_eq_iff _ _).1 he')
      obtain ⟨p,hp,hπp⟩ := hQP hq
      obtain ⟨w,hw⟩ := hdom (L.inv p) (hAi p (hPA hp)) a.val (hDA a.property)
      have hπw : π.toFun w = v.val := by
        have htarget : M.mulRel (π.toFun p) v.val (π.toFun a.val) := by
          rw [hπp]
          simpa only [M.inv_inv] using hM.right hqrel
        have hh := π.map_mul hw
        rw [π.map_inv] at hh
        exact M.inverse_cancel_left htarget hh
      have hwB : w ∈ B := hsmall w (hπw.symm ▸ hv)
      refine ⟨⟨w,hBD hwB⟩,hwB,?_⟩
      apply (D.project_eq_iff _ _).2
      exact (D.relation_iff _ _).2 ⟨L.inv p,hPi p hp,hd.right hw⟩
  · rintro _ ⟨v,hv,rfl⟩
    obtain ⟨x,hx⟩ := hthick v.val hv
    have hxB := hsmall x (hx.symm ▸ hv)
    refine ⟨D.project ⟨x,hBD hxB⟩,⟨⟨x,hBD hxB⟩,hxB,rfl⟩,?_⟩
    rw [D.localModelQuotientHom_projection]
    congr 1
    exact Subtype.ext hx
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
