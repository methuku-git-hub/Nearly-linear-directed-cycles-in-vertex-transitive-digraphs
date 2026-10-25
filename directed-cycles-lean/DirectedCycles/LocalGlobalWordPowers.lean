module

public import DirectedCycles.LocalWordPowers
public import DirectedCycles.EscapeSublevelPowers
public import DirectedCycles.WordBallBump

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Group G]

theorem ofGroup_wordPower (A : Set G) (n : ℕ) : (ofGroup G).wordPower A n = A^n := by
  ext x
  constructor
  · rintro ⟨l,hlen,hl,hp⟩
    have he : x = l.prod := (ofGroup_product_iff G l x).1 hp
    rw [he,← hlen]
    exact list_prod_mem_set_pow l hl
  · intro hx
    obtain ⟨l,hlen,hl,he⟩ := exists_list_of_mem_set_power hx
    exact ⟨l,hlen,hl,he ▸ ofGroup_product G l⟩

theorem ofGroup_allProductsDefined (A : Set G) (n : ℕ) : (ofGroup G).AllProductsDefined A n :=
  fun l _ _ => ⟨l.prod,ofGroup_product G l⟩

theorem ofGroup_setMul (A B : Set G) : (ofGroup G).setMul A B = A*B := by
  ext x
  rfl
end LocalGroupAlgebra
end DirectedCycles
