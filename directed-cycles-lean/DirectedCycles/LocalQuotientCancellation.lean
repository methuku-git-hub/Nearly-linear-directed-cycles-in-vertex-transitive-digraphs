module

public import DirectedCycles.LocalQuotientAssociativity

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalNormalSet
variable {G : Type*} [Group G] {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

theorem window_left_cancel {a b c d : W}
    (hac : (hP.windowSetoid hW1 hWi hW6).r a c)
    (hp : (a.val*b.val)*(c.val*d.val)⁻¹ ∈ P) :
    (hP.windowSetoid hW1 hWi hW6).r b d := by
  have hai := window_inv_mem hWi a.property
  have hci := window_inv_mem hWi c.property
  have hdi := window_inv_mem hWi d.property
  have hv : a.val⁻¹*((a.val*b.val)*(c.val*d.val)⁻¹)*(a.val⁻¹)⁻¹ ∈ V := by
    simpa [mul_inv_rev,mul_assoc] using window_four_mem hW1 hW6 b.property hdi hci a.property
  have hp1 := hP.conj_mem _ (window_mem hW1 hW6 hai) _ hp hv
  have hp2 := hP.window_inverse_respects hW1 hWi hW6 hac
  have hprod : (a.val⁻¹*((a.val*b.val)*(c.val*d.val)⁻¹)*(a.val⁻¹)⁻¹)*(a.val⁻¹*c.val) ∈ V := by
    simpa [mul_inv_rev,mul_assoc] using window_mul_mem hW1 hW6 b.property hdi
  have h := hP.mul_mem _ hp1 _ hp2 hprod
  change b.val*d.val⁻¹ ∈ P
  simpa [mul_inv_rev,mul_assoc] using h

theorem window_right_cancel {a b c d : W}
    (hbd : (hP.windowSetoid hW1 hWi hW6).r b d)
    (hp : (a.val*b.val)*(c.val*d.val)⁻¹ ∈ P) :
    (hP.windowSetoid hW1 hWi hW6).r a c := by
  have hbi := window_inv_mem hWi b.property
  have hci := window_inv_mem hWi c.property
  have hp0 : d.val*b.val⁻¹ ∈ P := by
    simpa only [mul_inv_rev,inv_inv] using hP.inv_mem _ hbd
  have hv : c.val*(d.val*b.val⁻¹)*c.val⁻¹ ∈ V := by
    simpa [mul_assoc] using window_four_mem hW1 hW6 c.property d.property hbi hci
  have hp1 := hP.conj_mem _ (window_mem hW1 hW6 c.property) _ hp0 hv
  have hprod : ((a.val*b.val)*(c.val*d.val)⁻¹)*(c.val*(d.val*b.val⁻¹)*c.val⁻¹) ∈ V := by
    simpa [mul_inv_rev,mul_assoc] using window_mul_mem hW1 hW6 a.property hci
  have h := hP.mul_mem _ hp _ hp1 hprod
  change a.val*c.val⁻¹ ∈ P
  simpa [mul_inv_rev,mul_assoc] using h

theorem quotient_left_cancel {a b c d : hP.WindowQuotient hW1 hWi hW6}
    (h₁ : hP.quotientMulRel hW1 hWi hW6 a b d)
    (h₂ : hP.quotientMulRel hW1 hWi hW6 a c d) : b = c := by
  obtain ⟨x,y,z,hx,hy,hz,hxy⟩ := h₁
  obtain ⟨x',y',z',hx',hy',hz',hxy'⟩ := h₂
  have hxx := Quotient.exact (hx.trans hx'.symm)
  have hzz : z.val*z'.val⁻¹ ∈ P := Quotient.exact (hz.trans hz'.symm)
  have hprod : (x.val*y.val)*(x'.val*y'.val)⁻¹ ∈ P := by simpa only [hxy,hxy'] using hzz
  rw [← hy,← hy']
  exact Quotient.sound (hP.window_left_cancel hW1 hWi hW6 hxx hprod)

theorem quotient_right_cancel {a b c d : hP.WindowQuotient hW1 hWi hW6}
    (h₁ : hP.quotientMulRel hW1 hWi hW6 b a d)
    (h₂ : hP.quotientMulRel hW1 hWi hW6 c a d) : b = c := by
  obtain ⟨x,y,z,hx,hy,hz,hxy⟩ := h₁
  obtain ⟨x',y',z',hx',hy',hz',hxy'⟩ := h₂
  have hyy := Quotient.exact (hy.trans hy'.symm)
  have hzz : z.val*z'.val⁻¹ ∈ P := Quotient.exact (hz.trans hz'.symm)
  have hprod : (x.val*y.val)*(x'.val*y'.val)⁻¹ ∈ P := by simpa only [hxy,hxy'] using hzz
  rw [← hx,← hx']
  exact Quotient.sound (hP.window_right_cancel hW1 hWi hW6 hyy hprod)

theorem quotient_inverse_product {a b c : hP.WindowQuotient hW1 hWi hW6}
    (h : hP.quotientMulRel hW1 hWi hW6 a b c) :
    hP.quotientMulRel hW1 hWi hW6 (hP.quotientInv hW1 hWi hW6 b)
      (hP.quotientInv hW1 hWi hW6 a) (hP.quotientInv hW1 hWi hW6 c) := by
  obtain ⟨x,y,z,rfl,rfl,rfl,hxy⟩ := h
  refine ⟨⟨y.val⁻¹,window_inv_mem hWi y.property⟩,⟨x.val⁻¹,window_inv_mem hWi x.property⟩,
    ⟨z.val⁻¹,window_inv_mem hWi z.property⟩,rfl,rfl,rfl,?_⟩
  simpa only [mul_inv_rev] using congrArg Inv.inv hxy

/-- The actual window quotient is cancellative as a local group. -/
theorem quotientAlgebra_cancellative : (hP.quotientAlgebra hW1 hWi hW6).Cancellative where
  left_cancel := hP.quotient_left_cancel hW1 hWi hW6
  right_cancel := hP.quotient_right_cancel hW1 hWi hW6
  inv_product h h' := hP.quotientMulRel_unique hW1 hWi hW6
    (hP.quotient_inverse_product hW1 hWi hW6 h) h'
end LocalNormalSet
end DirectedCycles
