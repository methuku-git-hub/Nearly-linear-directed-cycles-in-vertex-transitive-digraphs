module

public import DirectedCycles.LocalGroupReversal

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A defined product can be solved for either factor inside the actual local
multiplication domain. This is an existence property, stronger than equality
of values conditional on the inverse products already being defined. -/
structure DivisionClosed : Prop where
  left : ∀ {a b c}, L.mulRel a b c → L.mulRel (L.inv a) c b
  right : ∀ {a b c}, L.mulRel a b c → L.mulRel c (L.inv b) a

theorem ofGroup_divisionClosed (G : Type*) [Group G] : (ofGroup G).DivisionClosed where
  left := by
    intro a b c h
    change a⁻¹*c = b
    change a*b = c at h
    rw [← h,inv_mul_cancel_left]
  right := by
    intro a b c h
    change c*b⁻¹ = a
    change a*b = c at h
    rw [← h,mul_inv_cancel_right]

theorem DivisionClosed.restrict (hL : L.DivisionClosed) (S : Set G)
    (h1 : L.one ∈ S) (hi : ∀ x ∈ S, L.inv x ∈ S) :
    (L.restrict S h1 hi).DivisionClosed := ⟨fun h => hL.left h,fun h => hL.right h⟩

theorem DivisionClosed.cancellative (hL : L.DivisionClosed) (hr : L.Reversible) :
    L.Cancellative where
  left_cancel h h' := L.unique (hL.left h) (hL.left h')
  right_cancel h h' := L.unique (hL.right h) (hL.right h')
  inv_product h h' := L.unique (hr h) h'
end LocalGroupAlgebra

open scoped Pointwise
namespace LocalNormalSet
variable {G : Type*} [Group G] {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

/-- Actual local window quotients inherit both division domains. -/
theorem quotientAlgebra_divisionClosed :
    (hP.quotientAlgebra hW1 hWi hW6).DivisionClosed where
  left := by
    intro a b c h
    obtain ⟨x,y,z,rfl,rfl,rfl,hxy⟩ := h
    refine ⟨⟨x.val⁻¹,window_inv_mem hWi x.property⟩,z,y,rfl,rfl,rfl,?_⟩
    rw [← hxy,inv_mul_cancel_left]
  right := by
    intro a b c h
    obtain ⟨x,y,z,rfl,rfl,rfl,hxy⟩ := h
    refine ⟨z,⟨y.val⁻¹,window_inv_mem hWi y.property⟩,x,rfl,rfl,rfl,?_⟩
    rw [← hxy,mul_inv_cancel_right]
end LocalNormalSet

variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

theorem localUltraAlgebra_divisionClosed (hL : ∀ i, (L i).DivisionClosed) :
    (localUltraAlgebra F G L).DivisionClosed where
  left := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro a b c h
    apply (localUltraMulRel_mk_iff F G L _ _ _).2
    exact ((localUltraMulRel_mk_iff F G L a b c).1 h).mono fun i hi => (hL i).left hi
  right := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro a b c h
    apply (localUltraMulRel_mk_iff F G L _ _ _).2
    exact ((localUltraMulRel_mk_iff F G L a b c).1 h).mono fun i hi => (hL i).right hi
end DirectedCycles
