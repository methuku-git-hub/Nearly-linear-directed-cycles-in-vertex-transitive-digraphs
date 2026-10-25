module

public import DirectedCycles.LocalConjugationHom
public import DirectedCycles.LocalEscapeTrapping
public import DirectedCycles.LocalWordPowerMonotonicity

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem escapeNorm_antitone {A B : Set G} (hA : L.one ∈ A) (hAB : A ⊆ B) (g : G) :
    L.escapeNorm B g ≤ L.escapeNorm A g := by
  apply le_csInf (L.escapeValues_nonempty hA g)
  rintro r ⟨n,hn,rfl⟩
  apply L.escapeNorm_le_of_powers
  intro i hi
  obtain ⟨x,hx,hp⟩ := hn i hi
  exact ⟨x,hAB hx,hp⟩

theorem Product.triple_mem_wordPower {A : Set G} {N m n k : ℕ}
    (hdom : L.AllProductsDefined A N) (hsize : m+n+k ≤ N)
    {a b c z : G} (ha : a ∈ L.wordPower A m) (hb : b ∈ L.wordPower A n)
    (hc : c ∈ L.wordPower A k) (hp : L.Product [a,b,c] z) : z ∈ L.wordPower A (m+n+k) := by
  obtain ⟨u,v,hu,hv,hm⟩ := hp.split_allow_empty L (a := [a,b]) (b := [c]) rfl
  have hev := (Product.singleton_iff L).1 hv
  subst v
  have huA : u ∈ L.wordPower A (m+n) := by
    rw [L.wordPower_add hdom (by omega : m+n ≤ N)]
    exact ⟨a,ha,b,hb,(Product.pair_iff L _ _ _).1 hu⟩
  rw [L.wordPower_add hdom hsize]
  exact ⟨u,huA,c,hc,hm⟩

/-- Bounded conjugation of a local window, together with trapping, controls
escape. The powers transported by conjugation are actual finite local power
segments, with every intermediate value in the restricting window. -/
theorem escapeNorm_conjugate_of_trapping (hr : L.Reversible) {A B R : Set G}
    (hA : L.one ∈ A) (hi : ∀ x ∈ A, L.inv x ∈ A) (hAR : A ⊆ R)
    (hdom : L.AllProductsDefined R 6) {b : G} (hb : b ∈ R) (hbi : L.inv b ∈ R)
    (C : ℕ) (hC : 0 < C)
    (htrap : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ C → L.PowerIn B x j) → x ∈ A)
    (hconj : ∀ a ∈ A, ∀ c, L.Product [b,a,L.inv b] c → c ∈ B)
    {g c : G} (hgc : L.Product [b,g,L.inv b] c) :
    L.escapeNorm A c ≤ (C : ℝ)*L.escapeNorm A g := by
  by_cases hg : g ∈ A
  · obtain ⟨f,hf⟩ := L.exists_conjugationHom_on hr hA hi hAR hdom hb hbi
    have hfg : f.toFun ⟨g,hg⟩ = c := (hf ⟨g,hg⟩).unique L hgc
    have himage : Set.range f.toFun ⊆ B := by
      rintro x ⟨a,rfl⟩
      exact hconj a.val a.property _ (hf a)
    have hI1 : L.one ∈ Set.range f.toFun := ⟨⟨L.one,hA⟩,f.map_one⟩
    have he : L.escapeNorm B c ≤ L.escapeNorm A g := by
      rw [← hfg]
      exact (L.escapeNorm_antitone hI1 himage _).trans (L.escapeNorm_restricted_image_le hA hi f hg)
    exact (L.escapeNorm_le_mul_of_trapping (himage hI1) C hC htrap c).trans
      (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg C))
  · rw [L.escapeNorm_eq_one_of_not_mem hA hg,_root_.mul_one]
    exact (L.escapeNorm_le_one hA c).trans (by exact_mod_cast hC)

/-- The concrete 12-letter conjugator estimate required by the commutator
argument. Its conjugates occupy 25 letters, inside the 100-letter trap. -/
theorem escapeNorm_conjugate_twelve (hr : L.Reversible) {A : Set G}
    (hA : L.one ∈ A) (hi : ∀ x ∈ A, L.inv x ∈ A)
    (hdom : L.AllProductsDefined A 200) (C : ℕ) (hC : 0 < C)
    (htrap : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ C → L.PowerIn (L.wordPower A 100) x j) → x ∈ A)
    {y g c : G} (hy : y ∈ L.wordPower A 12) (hp : L.Product [L.inv y,g,y] c) :
    L.escapeNorm A c ≤ (C : ℝ)*L.escapeNorm A g := by
  have hAR : A ⊆ L.wordPower A 12 := by
    simpa only [L.wordPower_one] using L.wordPower_subset_wordPower hA hdom (by omega : 1 ≤ 12) (by omega)
  have hyi := L.inv_mem_wordPower hr hi hy
  apply L.escapeNorm_conjugate_of_trapping hr hA hi hAR (hdom.wordPower L (by omega : 12*6 ≤ 200))
    hyi (by simpa only [L.inv_inv] using hy) C hC htrap _ (by simpa only [L.inv_inv] using hp)
  intro a ha c hpc
  have ha1 : a ∈ L.wordPower A 1 := by rw [L.wordPower_one]; exact ha
  have ht := hpc.triple_mem_wordPower L hdom (by omega : 12+1+12 ≤ 200) hyi ha1
    (by simpa only [L.inv_inv] using hy)
  exact L.wordPower_subset_wordPower hA hdom (by omega : 25 ≤ 100) (by omega) ht
end LocalGroupAlgebra
end DirectedCycles
