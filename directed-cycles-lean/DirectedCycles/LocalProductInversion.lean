import DirectedCycles.LocalGroupHom
import DirectedCycles.LocalGroupReversal

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

def inversionHom (hL : L.Reversible) : LocalGroupHom L L.opposite where
  toFun := L.inv
  map_one := L.inv_one
  map_inv _ := rfl
  map_mul h := hL h

theorem opposite_opposite : L.opposite.opposite = L := by cases L; rfl

theorem Product.reverse_inv (hL : L.Reversible) {l : List G} {x : G}
    (h : L.Product l x) : L.Product (l.reverse.map L.inv) (L.inv x) := by
  have hh := (h.map (L.inversionHom hL)).reverse L.opposite
  rw [L.opposite_opposite] at hh
  simpa only [inversionHom,List.map_reverse] using hh
end LocalGroupAlgebra
end DirectedCycles
