import DirectedCycles.LocalWindowAssociativity
import DirectedCycles.LocalDivision
import DirectedCycles.LocalGroupHom

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace EquivalenceWindow
variable {G : Type*} {L : LocalGroupAlgebra G} {S W : Set G}
    (C : L.EquivalenceWindow S) (hWS : W ⊆ S)
    (hW1 : L.one ∈ W) (hWi : ∀ x ∈ W, L.inv x ∈ W)
    (hdom : L.AllProductsDefined W 3) (hW3 : L.wordPower W 3 ⊆ S)

/-- A genuine local quotient on the small window. Its product is defined
by actual small-window representatives, and associativity is proved by
comparison in the larger window. -/
def algebra : LocalGroupAlgebra (C.Carrier hWS) where
  one := C.project hWS ⟨L.one,hW1⟩
  inv := C.inv hWS hWi
  mulRel := C.mulRel hWS
  unique := C.mul_unique hWS
  one_mul := by
    intro x
    induction x using Quotient.inductionOn with
    | h x => exact ⟨⟨L.one,hW1⟩,x,x,rfl,rfl,rfl,L.one_mul x.val⟩
  mul_one := by
    intro x
    induction x using Quotient.inductionOn with
    | h x => exact ⟨x,⟨L.one,hW1⟩,x,rfl,rfl,rfl,L.mul_one x.val⟩
  inv_mul := by
    intro x
    induction x using Quotient.inductionOn with
    | h x => exact ⟨⟨L.inv x.val,hWi x.val x.property⟩,x,⟨L.one,hW1⟩,rfl,rfl,rfl,L.inv_mul x.val⟩
  mul_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h x => exact ⟨x,⟨L.inv x.val,hWi x.val x.property⟩,⟨L.one,hW1⟩,rfl,rfl,rfl,L.mul_inv x.val⟩
  assoc := C.mul_assoc hWS hW1 hdom hW3

def projectionHom : LocalGroupHom (L.restrict W hW1 hWi) (C.algebra hWS hW1 hWi hdom hW3) where
  toFun := C.project hWS
  map_one := rfl
  map_inv _ := rfl
  map_mul := fun {a b c} h => ⟨a,b,c,rfl,rfl,rfl,h⟩

theorem algebra_divisionClosed (hd : L.DivisionClosed) :
    (C.algebra hWS hW1 hWi hdom hW3).DivisionClosed where
  left := by
    intro a b c h
    obtain ⟨x,y,z,rfl,rfl,rfl,hm⟩ := h
    exact ⟨⟨L.inv x.val,hWi x.val x.property⟩,z,y,rfl,rfl,rfl,hd.left hm⟩
  right := by
    intro a b c h
    obtain ⟨x,y,z,rfl,rfl,rfl,hm⟩ := h
    exact ⟨z,⟨L.inv y.val,hWi y.val y.property⟩,x,rfl,rfl,rfl,hd.right hm⟩

theorem algebra_reversible (hr : L.Reversible) :
    (C.algebra hWS hW1 hWi hdom hW3).Reversible := by
  intro a b c h
  obtain ⟨x,y,z,rfl,rfl,rfl,hm⟩ := h
  exact ⟨⟨L.inv y.val,hWi y.val y.property⟩,⟨L.inv x.val,hWi x.val x.property⟩,
    ⟨L.inv z.val,hWi z.val z.property⟩,rfl,rfl,rfl,hr hm⟩

theorem algebra_cancellative (hd : L.DivisionClosed) (hr : L.Reversible) :
    (C.algebra hWS hW1 hWi hdom hW3).Cancellative :=
  DivisionClosed.cancellative _ (C.algebra_divisionClosed hWS hW1 hWi hdom hW3 hd)
    (C.algebra_reversible hWS hW1 hWi hdom hW3 hr)
end EquivalenceWindow
end LocalGroupAlgebra
end DirectedCycles
