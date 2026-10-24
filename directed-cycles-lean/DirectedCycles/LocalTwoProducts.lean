import DirectedCycles.LocalProductSplits

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem Product.pair_iff (x y z : G) : L.Product [x,y] z ↔ L.mulRel x y z := by
  constructor
  · intro h
    obtain ⟨a,b,ha,hb,hm⟩ := h.split L (a := [x]) (b := [y]) rfl (by simp) (by simp)
    have hea := (Product.singleton_iff L).1 ha
    have heb := (Product.singleton_iff L).1 hb
    simpa only [hea,heb] using hm
  · intro hm
    apply (product_iff_finite_splits L (by simp)).2
    intro k hk hk'
    have he : k.val = 1 := by simp only [List.length_cons,List.length_nil] at hk'; omega
    exact ⟨x,y,by simpa only [he,List.take_succ_cons,List.take_zero] using Product.singleton (L := L) x,
      by simpa only [he,List.drop_succ_cons,List.drop_zero] using Product.singleton (L := L) y,hm⟩
end LocalGroupAlgebra
end DirectedCycles
