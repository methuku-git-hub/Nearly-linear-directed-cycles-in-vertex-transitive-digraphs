import DirectedCycles.LocalQuotientOperations

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalNormalSet
variable {G : Type*} [Group G] {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

theorem quotient_assoc {a b c ab bc x y : hP.WindowQuotient hW1 hWi hW6}
    (hab : hP.quotientMulRel hW1 hWi hW6 a b ab)
    (hbc : hP.quotientMulRel hW1 hWi hW6 b c bc)
    (hx : hP.quotientMulRel hW1 hWi hW6 ab c x)
    (hy : hP.quotientMulRel hW1 hWi hW6 a bc y) : x = y := by
  obtain ⟨a1,b1,p1,ha1,hb1,hp1,hprod1⟩ := hab
  obtain ⟨b2,c2,p2,hb2,hc2,hp2,hprod2⟩ := hbc
  obtain ⟨p3,c3,zL,hp3,hc3,hzL,hprodL⟩ := hx
  obtain ⟨a4,p4,zR,ha4,hp4,hzR,hprodR⟩ := hy
  let t := a1.val*b1.val*c2.val
  let u := a1.val*b2.val*c2.val
  have hLt : zL.val*t⁻¹ ∈ P := by
    have h := hP.window_multiplication_respects hW1 hWi hW6
      (Quotient.exact (hp3.trans hp1.symm)) (Quotient.exact (hc3.trans hc2.symm))
    rw [hprodL,← hprod1] at h
    exact h
  have hRu : zR.val*u⁻¹ ∈ P := by
    have h := hP.window_multiplication_respects hW1 hWi hW6
      (Quotient.exact (ha4.trans ha1.symm)) (Quotient.exact (hp4.trans hp2.symm))
    rw [hprodR,← hprod2] at h
    simpa only [u,mul_assoc] using h
  have htu : t*u⁻¹ ∈ P := by
    apply hP.raw_rel_conjugate (Quotient.exact (hb1.trans hb2.symm)) (window_mem hW1 hW6 a1.property)
    simpa [mul_assoc] using window_four_mem hW1 hW6 a1.property b1.property
      (window_inv_mem hWi b2.property) (window_inv_mem hWi a1.property)
  have hLu : zL.val*u⁻¹ ∈ P := by
    apply hP.raw_rel_trans hLt htu
    simpa [u,mul_inv_rev,mul_assoc] using window_four_mem hW1 hW6 zL.property
      (window_inv_mem hWi c2.property) (window_inv_mem hWi b2.property) (window_inv_mem hWi a1.property)
  have huR : u*zR.val⁻¹ ∈ P := by
    simpa only [mul_inv_rev,inv_inv] using hP.inv_mem _ hRu
  have hLR : zL.val*zR.val⁻¹ ∈ P :=
    hP.raw_rel_trans hLu huR (window_mul_mem hW1 hW6 zL.property (window_inv_mem hWi zR.property))
  rw [← hzL,← hzR]
  exact Quotient.sound hLR

/-- The algebraic local quotient on the window, with its domain-sensitive
associativity proved from the actual coset relation. -/
def quotientAlgebra : LocalGroupAlgebra (hP.WindowQuotient hW1 hWi hW6) where
  one := hP.quotientOne hW1 hWi hW6
  inv := hP.quotientInv hW1 hWi hW6
  mulRel := hP.quotientMulRel hW1 hWi hW6
  unique := hP.quotientMulRel_unique hW1 hWi hW6
  one_mul := hP.quotient_one_mul hW1 hWi hW6
  mul_one := hP.quotient_mul_one hW1 hWi hW6
  inv_mul := hP.quotient_inv_mul hW1 hWi hW6
  mul_inv := hP.quotient_mul_inv hW1 hWi hW6
  assoc := hP.quotient_assoc hW1 hWi hW6
end LocalNormalSet
end DirectedCycles
