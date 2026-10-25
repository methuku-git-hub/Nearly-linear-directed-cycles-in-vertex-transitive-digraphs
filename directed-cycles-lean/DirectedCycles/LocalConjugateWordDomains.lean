module

public import DirectedCycles.LocalConjugates
public import DirectedCycles.LocalWordPowerIteration
public import DirectedCycles.LocalWordPowerMonotonicity
public import DirectedCycles.LocalTripleProducts

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem wordPower_mono_set {A B : Set G} (h : A ⊆ B) (n : ℕ) :
    L.wordPower A n ⊆ L.wordPower B n := by
  rintro x ⟨l,hlen,hl,hp⟩
  exact ⟨l,hlen,fun a ha => h (hl a ha),hp⟩

/-- Actual conjugates by four-letter words are nine-letter values. No
global multiplication or representative-independent domain is assumed. -/
theorem conjugates_subset_wordPower_nine (hr : L.Reversible) {A S : Set G} {N : ℕ}
    (hi : ∀ x ∈ A, L.inv x ∈ A)
    (hd : L.AllProductsDefined A N) (hN : 9 ≤ N) (hSA : S ⊆ A) :
    L.conjugates S (L.wordPower A 4) ⊆ L.wordPower A 9 := by
  rintro x ⟨s,hs,b,hb,hp⟩
  have hbi := L.inv_mem_wordPower hr hi hb
  obtain ⟨u,v,hu,hv,hm⟩ := hp.split_allow_empty L (show [L.inv b,s,b] = [L.inv b,s]++[b] from rfl)
  have hvb : v = b := (Product.singleton_iff L).1 hv
  have hpair : L.mulRel (L.inv b) s u := (Product.pair_iff L _ _ _).1 hu
  have hu5 : u ∈ L.wordPower A 5 := by
    rw [show 5 = 4+1 from rfl,L.wordPower_add hd (by omega),L.wordPower_one]
    exact ⟨L.inv b,hbi,s,hSA hs,hpair⟩
  rw [show 9 = 5+4 from rfl,L.wordPower_add hd (by omega)]
  exact ⟨u,hu5,b,hb,by simpa only [hvb] using hm⟩

/-- A single long source-word domain supplies all required products of
conjugates and places their values in the corresponding source word window. -/
theorem conjugate_word_domains (hr : L.Reversible) {A S : Set G} {N m : ℕ}
    (hi : ∀ x ∈ A, L.inv x ∈ A)
    (hd : L.AllProductsDefined A N) (hN : 9 ≤ N) (hm : 9*m ≤ N) (hSA : S ⊆ A) :
    L.AllProductsDefined (L.conjugates S (L.wordPower A 4)) m ∧
    L.wordPower (L.conjugates S (L.wordPower A 4)) m ⊆ L.wordPower A (9*m) := by
  have hQ := L.conjugates_subset_wordPower_nine hr hi hd hN hSA
  refine ⟨(hd.wordPower L hm).mono L hQ le_rfl,?_⟩
  exact (L.wordPower_mono_set hQ m).trans (L.wordPower_wordPower_subset hd 9 m hm)
end LocalGroupAlgebra
end DirectedCycles
