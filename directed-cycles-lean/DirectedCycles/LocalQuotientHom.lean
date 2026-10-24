import DirectedCycles.LocalGroupHom
import DirectedCycles.LocalQuotientAssociativity

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalNormalSet
variable {G : Type*} [Group G] {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

/-- The actual projection from the restricted ambient group to the quotient is
a local homomorphism. -/
def quotientHom : LocalGroupHom
    ((LocalGroupAlgebra.ofGroup G).restrict W hW1 (fun _ hx => window_inv_mem hWi hx))
    (hP.quotientAlgebra hW1 hWi hW6) where
  toFun := hP.windowMk hW1 hWi hW6
  map_one := rfl
  map_inv _ := rfl
  map_mul := by
    intro a b c h
    exact ⟨a,b,c,rfl,rfl,rfl,h⟩

theorem quotientHom_kernel (a : W) :
    (hP.quotientHom hW1 hWi hW6).toFun a = (hP.quotientAlgebra hW1 hWi hW6).one ↔ a.val ∈ P := by
  change hP.windowMk hW1 hWi hW6 a = hP.windowMk hW1 hWi hW6 ⟨1,hW1⟩ ↔ a.val ∈ P
  rw [window_quotient_eq_iff]
  simp

theorem quotientHom_product {l : List W} {x : W}
    (h : ((LocalGroupAlgebra.ofGroup G).restrict W hW1 (fun _ hx => window_inv_mem hWi hx)).Product l x) :
    (hP.quotientAlgebra hW1 hWi hW6).Product (l.map (hP.windowMk hW1 hWi hW6))
      (hP.windowMk hW1 hWi hW6 x) :=
  h.map (hP.quotientHom hW1 hWi hW6)
end LocalNormalSet
end DirectedCycles
