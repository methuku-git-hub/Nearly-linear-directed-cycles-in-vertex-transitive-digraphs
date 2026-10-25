module

public import DirectedCycles.LocalQuotientWindow

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalNormalSet
variable {G : Type*} [Group G] {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

abbrev windowMk (a : W) : hP.WindowQuotient hW1 hWi hW6 :=
  Quotient.mk (hP.windowSetoid hW1 hWi hW6) a

def quotientOne : hP.WindowQuotient hW1 hWi hW6 := hP.windowMk hW1 hWi hW6 ⟨1,hW1⟩

def quotientInv : hP.WindowQuotient hW1 hWi hW6 → hP.WindowQuotient hW1 hWi hW6 :=
  Quotient.map (fun a : W => ⟨a.val⁻¹,window_inv_mem hWi a.property⟩)
    (by
      intro a b hab
      change a.val⁻¹*(b.val⁻¹)⁻¹ ∈ P
      simpa only [inv_inv] using hP.window_inverse_respects hW1 hWi hW6 hab)

/-- A quotient multiplication is defined only if some pair of representatives
has its actual product inside the window. -/
def quotientMulRel (x y z : hP.WindowQuotient hW1 hWi hW6) : Prop :=
  ∃ a b c : W, hP.windowMk hW1 hWi hW6 a = x ∧
    hP.windowMk hW1 hWi hW6 b = y ∧ hP.windowMk hW1 hWi hW6 c = z ∧
      a.val*b.val = c.val

theorem quotientMulRel_unique {x y z t : hP.WindowQuotient hW1 hWi hW6}
    (hz : hP.quotientMulRel hW1 hWi hW6 x y z) (ht : hP.quotientMulRel hW1 hWi hW6 x y t) : z = t := by
  obtain ⟨a,b,c,ha,hb,hc,hab⟩ := hz
  obtain ⟨d,e,f,hd,he,hf,hde⟩ := ht
  rw [← hc,← hf]
  apply Quotient.sound
  have had := Quotient.exact (ha.trans hd.symm)
  have hbe := Quotient.exact (hb.trans he.symm)
  have hprod := hP.window_multiplication_respects hW1 hWi hW6 had hbe
  change c.val*f.val⁻¹ ∈ P
  simpa only [hab,hde] using hprod

theorem quotient_one_mul (x : hP.WindowQuotient hW1 hWi hW6) :
    hP.quotientMulRel hW1 hWi hW6 (hP.quotientOne hW1 hWi hW6) x x := by
  induction x using Quotient.inductionOn with
  | h a => exact ⟨⟨1,hW1⟩,a,a,rfl,rfl,rfl,by simp⟩

theorem quotient_mul_one (x : hP.WindowQuotient hW1 hWi hW6) :
    hP.quotientMulRel hW1 hWi hW6 x (hP.quotientOne hW1 hWi hW6) x := by
  induction x using Quotient.inductionOn with
  | h a => exact ⟨a,⟨1,hW1⟩,a,rfl,rfl,rfl,by simp⟩

theorem quotient_inv_mul (x : hP.WindowQuotient hW1 hWi hW6) :
    hP.quotientMulRel hW1 hWi hW6 (hP.quotientInv hW1 hWi hW6 x) x (hP.quotientOne hW1 hWi hW6) := by
  induction x using Quotient.inductionOn with
  | h a => exact ⟨⟨a.val⁻¹,window_inv_mem hWi a.property⟩,a,⟨1,hW1⟩,rfl,rfl,rfl,by simp⟩

theorem quotient_mul_inv (x : hP.WindowQuotient hW1 hWi hW6) :
    hP.quotientMulRel hW1 hWi hW6 x (hP.quotientInv hW1 hWi hW6 x) (hP.quotientOne hW1 hWi hW6) := by
  induction x using Quotient.inductionOn with
  | h a => exact ⟨a,⟨a.val⁻¹,window_inv_mem hWi a.property⟩,⟨1,hW1⟩,rfl,rfl,rfl,by simp⟩

include hP in
/-- Transitivity for raw representatives, with the precise final-product
containment needed to use local closure. -/
theorem raw_rel_trans {a b c : G} (hab : a*b⁻¹ ∈ P) (hbc : b*c⁻¹ ∈ P)
    (hac : a*c⁻¹ ∈ V) : a*c⁻¹ ∈ P := by
  have hv : (a*b⁻¹)*(b*c⁻¹) ∈ V := by simpa [mul_assoc] using hac
  simpa [mul_assoc] using hP.mul_mem _ hab _ hbc hv

include hP in
/-- Equality of representatives remains valid after inserting the same prefix
and suffix, provided the requisite product stays in the normalizing neighbourhood. -/
theorem raw_rel_conjugate {a b c d : G} (hab : a*b⁻¹ ∈ P) (hc : c ∈ V)
    (hcv : c*(a*b⁻¹)*c⁻¹ ∈ V) : (c*a*d)*(c*b*d)⁻¹ ∈ P := by
  simpa [mul_inv_rev,mul_assoc] using hP.conj_mem _ hc _ hab hcv
end LocalNormalSet
end DirectedCycles
