module

public import DirectedCycles.LocalCentralModelQuotientMap
public import DirectedCycles.LocalDivision
public import DirectedCycles.LocalQuotientTopology

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G H : Type*} {L : LocalGroupAlgebra G} [Group H] {P : Set G}
    (D : L.CentralQuotientData P) {Q T W : Set H} (hQ : LocalNormalSet Q T)
    (hW1 : (1 : H) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ T)

/-- Small and thick neighbourhoods descend to the actual central quotient.
A target central difference is lifted through the exact progression image;
an actual source correction then enters the inner source neighbourhood. -/
theorem modelQuotientHom_neighbourhood (hd : L.DivisionClosed)
    (π : LocalGroupHom L (LocalGroupAlgebra.ofGroup H))
    (hPQ : ∀ p ∈ P, π.toFun p ∈ Q) (hDW : ∀ x ∈ D.small, π.toFun x ∈ W)
    (hQP : Q ⊆ π.toFun '' P) (hPi : ∀ p ∈ P, L.inv p ∈ P)
    (A B : Set G) (hPA : P ⊆ A) (hDA : D.small ⊆ A)
    (hAi : ∀ x ∈ A, L.inv x ∈ A) (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y)
    (hBD : B ⊆ D.small) (V : Set H)
    (hsmall : ∀ x, π.toFun x ∈ V → x ∈ B)
    (hthick : ∀ v ∈ V, ∃ x, π.toFun x = v) :
    let Vq := hQ.windowMk hW1 hWi hW6 '' {v : W | v.val ∈ V}
    (D.modelQuotientHom hQ hW1 hWi hW6 π hPQ hDW).toFun ⁻¹' Vq ⊆
      D.project '' {x : D.small | x.val ∈ B} ∧
    Vq ⊆ (D.modelQuotientHom hQ hW1 hWi hW6 π hPQ hDW).toFun ''
      (D.project '' {x : D.small | x.val ∈ B}) := by
  intro Vq
  constructor
  · intro y hy
    induction y using Quotient.inductionOn with
    | h a =>
      obtain ⟨v,hv,he⟩ := hy
      have he' : hQ.windowMk hW1 hWi hW6 ⟨π.toFun a.val,hDW a.val a.property⟩ =
          hQ.windowMk hW1 hWi hW6 v := he.symm
      have hdiff : π.toFun a.val*v.val⁻¹ ∈ Q :=
        (LocalNormalSet.window_quotient_eq_iff hQ hW1 hWi hW6 _ _).1 he'
      obtain ⟨p,hp,hπp⟩ := hQP hdiff
      obtain ⟨w,hw⟩ := hdom (L.inv p) (hAi p (hPA hp)) a.val (hDA a.property)
      have hπw : π.toFun w = v.val := by
        have hh := π.map_mul hw
        rw [π.map_inv] at hh
        change (π.toFun p)⁻¹*π.toFun a.val = π.toFun w at hh
        rw [hπp] at hh
        simpa only [_root_.mul_inv_rev,_root_.inv_inv,_root_.mul_assoc,_root_.inv_mul_cancel,_root_.mul_one] using hh.symm
      have hwB : w ∈ B := hsmall w (hπw.symm ▸ hv)
      refine ⟨⟨w,hBD hwB⟩,hwB,?_⟩
      apply (D.project_eq_iff _ _).2
      exact (D.relation_iff _ _).2 ⟨L.inv p,hPi p hp,hd.right hw⟩
  · rintro _ ⟨v,hv,rfl⟩
    obtain ⟨x,hx⟩ := hthick v.val hv
    have hxB := hsmall x (hx.symm ▸ hv)
    refine ⟨D.project ⟨x,hBD hxB⟩,⟨⟨x,hBD hxB⟩,hxB,rfl⟩,?_⟩
    rw [D.modelQuotientHom_projection]
    congr 1
    exact Subtype.ext hx
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
