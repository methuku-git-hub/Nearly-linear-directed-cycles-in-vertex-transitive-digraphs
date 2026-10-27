module

public import DirectedCycles.LocalConvolutionPowerSupport
public import DirectedCycles.LocalUnregularizedEscapeBump
public import DirectedCycles.LocalConjugateEscape
public import DirectedCycles.LocalCommutatorDerivative
public import DirectedCycles.LocalEscapeDerivativeBound

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

/-- The finite local commutator estimate. Bumps, conjugation of power
segments, convolution supports and the isometry used in the commutator
identity all have their actual domains proved. -/
theorem finite_gleason_commutator (hd : L.DivisionClosed) (hr : L.Reversible)
    (A : Finset G) {K : ℕ} (hA : IsLocalFiniteApproximateGroup L K A)
    (C : ℕ) (hC : 0 < C)
    (hfirst : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ C → L.PowerIn (L.wordPower (A : Set G) 100) x j) → x ∈ A)
    {P : ℝ} (hP : 0 < P)
    (hreg : ∀ ε : ℝ, 0 < ε → ∀ x, L.escapeNorm A x ≤ P*L.restrictedEscapeDistance A ε x)
    {g h k : G} (hg : g ∈ L.wordPower (A : Set G) 10) (hh : h ∈ L.wordPower (A : Set G) 10)
    (hk : L.Product [L.inv g,L.inv h,g,h] k) :
    L.escapeNorm A k ≤ (2*(C : ℝ)^2*(K : ℝ)^11*P^2)*L.escapeNorm A g*L.escapeNorm A h := by
  classical
  have hc := hd.cancellative L hr
  have hCr : 0 ≤ (C : ℝ) := Nat.cast_nonneg C
  have hsub : ∀ {m n : ℕ}, m ≤ n → n ≤ 200 →
      L.wordPower (A : Set G) m ⊆ L.wordPower (A : Set G) n :=
    fun {_ _} hmn hn => L.wordPower_subset_wordPower hA.one_mem hA.allProducts hmn hn
  have hA4 : L.one ∈ L.wordPower (A : Set G) 4 := by
    apply hsub (by omega : 1 ≤ 4) (by omega)
    rw [L.wordPower_one]
    exact hA.one_mem
  have htrap4 : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ C → L.PowerIn (L.wordPower (A : Set G) 4) x j) → x ∈ A := by
    intro x hx
    apply hfirst
    intro j hj hj'
    obtain ⟨y,hy,hp⟩ := hx j hj hj'
    exact ⟨y,hsub (by omega : 4 ≤ 100) (by omega) hy,hp⟩
  obtain ⟨φ,hφ,hφA,hφs,hφlip⟩ := L.exists_unregularized_escape_bump hd hr A hA.one_mem hA.inv_mem
    (hA.allProducts.mono L (Set.Subset.refl _) (by omega : 3 ≤ 200)) hP hreg
  have hφd : ∀ x, L.derivativeNorm φ x ≤ P*L.escapeNorm A x := by
    intro x
    exact (L.derivativeNorm_le_iff _ _ (mul_nonneg hP.le (L.escapeNorm_nonneg hA.one_mem x))).2 (hφlip x)
  let f := L.normalizedConvolution A φ φ
  have hf1 : 1 ≤ f L.one := L.normalizedConvolution_one hc A hA.one_mem hA.inv_mem
    (fun x => (hφ x).1) (fun x => (hφ x).1) hφA hφA
  have hfs : ∀ x, x ∉ L.wordPower (A : Set G) 4 → f x = 0 :=
    fun _ hx => L.normalizedConvolution_support hc
      (hA.allProducts.mono L (Set.Subset.refl _) (by omega : 4 ≤ 200)) hφs hφs hx
  have hB : ∀ x ∈ L.wordPower (A : Set G) 4, ∀ y ∈ L.wordPower (A : Set G) 4, L.Defined x y := by
    intro x hx y hy
    obtain ⟨z,hz⟩ := (hA.allProducts.wordPower L (by omega : 4*2 ≤ 200)) [x,y] (by simp) (by aesop)
    exact ⟨z,(Product.pair_iff L _ _ _).1 hz⟩
  have he : ∀ x, L.escapeNorm A x ≤ (C : ℝ)*L.derivativeNorm f x :=
    L.escapeNorm_le_mul_derivativeNorm hc hA4 hB C hC htrap4 f hf1 hfs
  have htwo : ∀ a ∈ L.wordPower (A : Set G) 10, ∀ b ∈ L.wordPower (A : Set G) 10,
      L.derivativeNorm (L.derivative a f) b ≤
        (C : ℝ)*(K : ℝ)^11*P^2*L.escapeNorm A a*L.escapeNorm A b := by
    intro a ha b hb
    have hb0 := L.escapeNorm_nonneg hA.one_mem b
    have hbnd : ∀ y ∈ L.wordPower (A : Set G) 12,
        ∃ c ∈ L.wordPower (A : Set G) 34, ∃ t,
          L.mulRel b y t ∧ L.mulRel y c t ∧ L.derivativeNorm φ c ≤ P*((C : ℝ)*L.escapeNorm A b) := by
      intro y hy
      have hyi := L.inv_mem_wordPower hr hA.inv_mem hy
      have hb12 := hsub (by omega : 10 ≤ 12) (by omega) hb
      obtain ⟨c,hpc⟩ := (hA.allProducts.wordPower L (by omega : 12*3 ≤ 200))
        [L.inv y,b,y] (by simp) (by aesop)
      have hc34 : c ∈ L.wordPower (A : Set G) 34 :=
        hpc.triple_mem_wordPower L hA.allProducts (by omega : 12+10+12 ≤ 200) hyi hb hy
      obtain ⟨u,t,hu,ht,hm⟩ := hpc.split_allow_empty L (a := [L.inv y]) (b := [b,y]) rfl
      have heu := (Product.singleton_iff L).1 hu
      subst u
      have hct : L.mulRel y c t := by simpa only [L.inv_inv] using hd.left hm
      refine ⟨c,hc34,t,(Product.pair_iff L _ _ _).1 ht,hct,?_⟩
      exact (hφd c).trans (mul_le_mul_of_nonneg_left
        (L.escapeNorm_conjugate_twelve hr hA.one_mem hA.inv_mem hA.allProducts C hC hfirst hy hpc) hP.le)
    calc
      L.derivativeNorm (L.derivative a f) b ≤
          (K : ℝ)^11*L.derivativeNorm φ a*(P*((C : ℝ)*L.escapeNorm A b)) :=
        L.derivativeNorm_twice_normalizedConvolution_ten_le hc hA hφs hφs ha hb
          (mul_nonneg hP.le (mul_nonneg hCr hb0)) hbnd
      _ ≤ (K : ℝ)^11*(P*L.escapeNorm A a)*(P*((C : ℝ)*L.escapeNorm A b)) := by
        gcongr
        exact hφd a
      _ = (C : ℝ)*(K : ℝ)^11*P^2*L.escapeNorm A a*L.escapeNorm A b := by ring
  have hgi := L.inv_mem_wordPower hr hA.inv_mem hg
  have hhi := L.inv_mem_wordPower hr hA.inv_mem hh
  have hten := hA.allProducts.wordPower L (by omega : 10*6 ≤ 200)
  obtain ⟨r,hpr⟩ := hten [h,g] (by simp) (by aesop)
  obtain ⟨s,hps⟩ := hten [g,h] (by simp) (by aesop)
  have hmr := (Product.pair_iff L _ _ _).1 hpr
  have hms := (Product.pair_iff L _ _ _).1 hps
  have hr20 : r ∈ L.wordPower (A : Set G) 20 := by
    rw [show 20 = 10+10 by rfl,L.wordPower_add hA.allProducts (by omega)]
    exact ⟨h,hh,g,hg,hmr⟩
  have hk40 : k ∈ L.wordPower (A : Set G) 40 := by
    obtain ⟨u,v,hu,hv,hm⟩ := hk.split_allow_empty L (a := [L.inv g,L.inv h]) (b := [g,h]) rfl
    have hu20 : u ∈ L.wordPower (A : Set G) 20 := by
      rw [show 20 = 10+10 by rfl,L.wordPower_add hA.allProducts (by omega)]
      exact ⟨L.inv g,hgi,L.inv h,hhi,(Product.pair_iff L _ _ _).1 hu⟩
    have hv20 : v ∈ L.wordPower (A : Set G) 20 := by
      rw [show 20 = 10+10 by rfl,L.wordPower_add hA.allProducts (by omega)]
      exact ⟨g,hg,h,hh,(Product.pair_iff L _ _ _).1 hv⟩
    rw [show 40 = 20+20 by rfl,L.wordPower_add hA.allProducts (by omega)]
    exact ⟨u,hu20,v,hv20,hm⟩
  have hrk := L.commutator_multiplication hten hg hh hgi hhi hmr hms hk
  have hfR : ∀ x, f x ≠ 0 → x ∈ L.wordPower (A : Set G) 40 := by
    intro x hx
    by_contra hn
    exact hx (hfs x (fun h => hn (hsub (by omega : 4 ≤ 40) (by omega) h)))
  have hder := L.derivativeNorm_commutator_le hc (hA.allProducts.wordPower L (by omega : 40*3 ≤ 200))
    (hsub (by omega : 10 ≤ 40) (by omega) hg) (hsub (by omega : 10 ≤ 40) (by omega) hh)
    (hsub (by omega : 20 ≤ 40) (by omega) hr20) hk40 hmr hms hrk f hfR
  have h1 := htwo h hh g hg
  have h2 := htwo g hg h hh
  have hsum : L.derivativeNorm f k ≤ 2*(C : ℝ)*(K : ℝ)^11*P^2*L.escapeNorm A g*L.escapeNorm A h := by
    nlinarith
  calc
    L.escapeNorm A k ≤ (C : ℝ)*L.derivativeNorm f k := he k
    _ ≤ (C : ℝ)*(2*(C : ℝ)*(K : ℝ)^11*P^2*L.escapeNorm A g*L.escapeNorm A h) :=
      mul_le_mul_of_nonneg_left hsum hCr
    _ = (2*(C : ℝ)^2*(K : ℝ)^11*P^2)*L.escapeNorm A g*L.escapeNorm A h := by ring
end LocalGroupAlgebra
end DirectedCycles
