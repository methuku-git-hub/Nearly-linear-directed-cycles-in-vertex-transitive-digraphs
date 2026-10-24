import DirectedCycles.LocalNormalSubgroupQuotient
import DirectedCycles.LocalSubgroupTransport

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace NormalSubgroupWindow
variable {G : Type*} {L : LocalGroupAlgebra G} {H S : Set G}
    (W : L.NormalSubgroupWindow H S) (hd : L.DivisionClosed) (hr : L.Reversible)

theorem project_eq_one_iff (x : S) :
    (W.congruence hd hr).project x = (W.congruence hd hr).algebra.one ↔ x.val ∈ H := by
  change Quotient.mk (W.setoid hd) x = Quotient.mk (W.setoid hd) ⟨L.one,W.one_mem⟩ ↔ x.val ∈ H
  rw [Quotient.eq]
  constructor
  · rintro ⟨h,hh,hm⟩
    have he : x.val = h := L.unique hm (L.mul_one h)
    exact he.symm ▸ hh
  · intro hx
    exact ⟨x.val,hx,L.mul_one x.val⟩

/-- If all global subgroups of the window lie in H, quotienting by H gives
an NSS local group. No finiteness or choice of an ambient global group is used. -/
theorem quotient_isNSS
    (hmax : ∀ T : Set G, L.IsGlobalSubgroup T → T ⊆ S → T ⊆ H) :
    (W.congruence hd hr).algebra.IsNSS Set.univ := by
  let C := W.congruence hd hr
  intro Q hQ _ x hx
  obtain ⟨a,rfl⟩ := Quotient.exists_rep x
  let T : Set G := Subtype.val '' (C.project ⁻¹' Q)
  have hT : L.IsGlobalSubgroup T :=
    (C.preimage_isGlobalSubgroup hQ).image (LocalGroupHom.inclusion L S W.one_mem W.inv_mem)
  have hTS : T ⊆ S := by rintro y ⟨b,_,rfl⟩; exact b.property
  have haT : a.val ∈ T := ⟨a,hx,rfl⟩
  exact (W.project_eq_one_iff hd hr a).2 (hmax T hT hTS haT)

/-- A trapping assertion and the exact zero-escape characterization prove
maximality of H, hence NSS of the actual local quotient. -/
theorem zero_escape_quotient_isNSS {A : Set G} (hA : L.one ∈ A)
    (hH : H = {x | L.escapeNorm A x = 0})
    (htrap : ∀ T : Set G, L.IsGlobalSubgroup T → T ⊆ S → T ⊆ A) :
    (W.congruence hd hr).algebra.IsNSS Set.univ := by
  apply W.quotient_isNSS hd hr
  intro T hT hTS x hx
  rw [hH]
  exact hT.escapeNorm_eq_zero (htrap T hT hTS) hA hx
end NormalSubgroupWindow
end LocalGroupAlgebra
end DirectedCycles
