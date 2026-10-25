module

public import DirectedCycles.LocalSubgroupTransport
public import DirectedCycles.LocalWordPowers

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} {L : LocalGroupAlgebra G} {H : Set G}

theorem IsGlobalSubgroup.product_mem (hH : L.IsGlobalSubgroup H)
    {l : List G} {x : G} (hp : L.Product l x) (hl : ∀ a ∈ l, a ∈ H) : x ∈ H := by
  induction l generalizing x with
  | nil => exact ((Product.nil_iff L).1 hp).symm ▸ hH.one_mem
  | cons a l ih =>
    obtain ⟨u,v,hu,hv,hm⟩ := hp.split_allow_empty L (a := [a]) (b := l) rfl
    have he := (Product.singleton_iff L).1 hu
    subst u
    have hvH := ih hv (fun b hb => hl b (List.mem_cons_of_mem a hb))
    obtain ⟨z,hz,hmz⟩ := hH.mul_total a (hl a (List.mem_cons_self ..)) v hvH
    exact (L.unique hm hmz).symm ▸ hz

theorem IsGlobalSubgroup.wordPower_subset (hH : L.IsGlobalSubgroup H) (n : ℕ) : L.wordPower H n ⊆ H := by
  rintro x ⟨l,_,hl,hp⟩
  exact hH.product_mem hp hl
end LocalGroupAlgebra
end DirectedCycles
