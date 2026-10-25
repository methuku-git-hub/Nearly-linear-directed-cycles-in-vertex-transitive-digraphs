module

public import DirectedCycles.LocalTwoProducts
public import DirectedCycles.LocalWordPowers

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem AllProductsDefined.mono {A B : Set G} {M N : ℕ}
    (h : L.AllProductsDefined A N) (hBA : B ⊆ A) (hMN : M ≤ N) :
    L.AllProductsDefined B M :=
  fun l hl hm => h l (hl.trans hMN) (fun a ha => hBA (hm a ha))

/-- A fully defined triple supplies both associativity domains for any given
values of its two overlapping two-letter products. -/
theorem AllProductsDefined.triple {A : Set G} (h : L.AllProductsDefined A 3)
    {a b c ab bc : G} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : L.mulRel a b ab) (hbc : L.mulRel b c bc) :
    ∃ z, L.mulRel ab c z ∧ L.mulRel a bc z := by
  obtain ⟨z,hz⟩ := h [a,b,c] (by simp) (by aesop)
  obtain ⟨u,v,hu,hv,hm⟩ := hz.split L (a := [a,b]) (b := [c]) rfl (by simp) (by simp)
  have heu : u = ab := L.unique ((Product.pair_iff L a b u).1 hu) hab
  have hev : v = c := (Product.singleton_iff L).1 hv
  have habc : L.mulRel ab c z := by simpa only [heu,hev] using hm
  obtain ⟨u',v',hu',hv',hm'⟩ := hz.split L (a := [a]) (b := [b,c]) rfl (by simp) (by simp)
  have heu' : u' = a := (Product.singleton_iff L).1 hu'
  have hev' : v' = bc := L.unique ((Product.pair_iff L b c v').1 hv') hbc
  exact ⟨z,habc,by simpa only [heu',hev'] using hm'⟩
end LocalGroupAlgebra
end DirectedCycles
