import DirectedCycles.LocalTripleProducts

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem Product.triple_of_rel {a b c u v z : G}
    (hab : L.mulRel a b u) (hbc : L.mulRel b c v)
    (huc : L.mulRel u c z) (hav : L.mulRel a v z) : L.Product [a,b,c] z := by
  apply (L.product_iff_finite_splits (by simp)).2
  intro k hk hk'
  have he : k.val = 1 ∨ k.val = 2 := by
    simp only [List.length_cons,List.length_nil] at hk'
    omega
  rcases he with he | he
  · refine ⟨a,v,?_,?_,hav⟩
    · simpa only [he,List.take_succ_cons,List.take_zero] using Product.singleton (L := L) a
    · simpa only [he,List.drop_succ_cons,List.drop_zero] using (Product.pair_iff L _ _ _).2 hbc
  · refine ⟨u,c,?_,?_,huc⟩
    · simpa only [he,List.take_succ_cons,List.take_zero] using (Product.pair_iff L _ _ _).2 hab
    · simpa only [he,List.drop_succ_cons,List.drop_zero] using Product.singleton (L := L) c

theorem product_one_sandwich (x : G) : L.Product [L.one,x,L.one] x :=
  Product.triple_of_rel L (L.one_mul x) (L.mul_one x) (L.mul_one x) (L.one_mul x)

/-- Conjugates consist of actual all-bracketings local triples. -/
def conjugates (S B : Set G) : Set G :=
  {x | ∃ s ∈ S, ∃ b ∈ B, L.Product [L.inv b,s,b] x}

theorem inv_mem_conjugates (hr : L.Reversible) {S B : Set G}
    (hS : ∀ s ∈ S, L.inv s ∈ S) {x : G} (hx : x ∈ L.conjugates S B) :
    L.inv x ∈ L.conjugates S B := by
  obtain ⟨s,hs,b,hb,hp⟩ := hx
  refine ⟨L.inv s,hS s hs,b,hb,?_⟩
  simpa only [List.reverse_cons,List.reverse_nil,List.nil_append,List.map_append,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,L.inv_inv] using hp.reverse_inv L hr

theorem subset_conjugates {S B : Set G} (hB : L.one ∈ B) : S ⊆ L.conjugates S B := by
  intro s hs
  exact ⟨s,hs,L.one,hB,by simpa only [L.inv_one] using L.product_one_sandwich s⟩
end LocalGroupAlgebra
end DirectedCycles
