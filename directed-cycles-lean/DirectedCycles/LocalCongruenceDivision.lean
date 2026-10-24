import DirectedCycles.LocalGroupCongruence
import DirectedCycles.LocalDivision

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupCongruence
variable {G : Type*} {L : LocalGroupAlgebra G} (C : LocalGroupCongruence L)

theorem algebra_reversible (hL : L.Reversible) : C.algebra.Reversible := by
  intro a b c h
  obtain ⟨x,y,z,rfl,rfl,rfl,hxy⟩ := h
  exact ⟨L.inv y,L.inv x,L.inv z,rfl,rfl,rfl,hL hxy⟩

theorem algebra_divisionClosed (hL : L.DivisionClosed) : C.algebra.DivisionClosed where
  left := by
    intro a b c h
    obtain ⟨x,y,z,rfl,rfl,rfl,hxy⟩ := h
    exact ⟨L.inv x,z,y,rfl,rfl,rfl,hL.left hxy⟩
  right := by
    intro a b c h
    obtain ⟨x,y,z,rfl,rfl,rfl,hxy⟩ := h
    exact ⟨z,L.inv y,x,rfl,rfl,rfl,hL.right hxy⟩

theorem algebra_cancellative (hL : L.DivisionClosed) (hr : L.Reversible) :
    C.algebra.Cancellative :=
  (C.algebra_divisionClosed hL).cancellative C.algebra (C.algebra_reversible hr)
end LocalGroupCongruence
end DirectedCycles
