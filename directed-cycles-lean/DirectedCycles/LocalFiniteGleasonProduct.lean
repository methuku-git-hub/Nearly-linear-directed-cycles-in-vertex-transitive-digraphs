module

public import DirectedCycles.LocalNormalizedDerivativeBounds
public import DirectedCycles.LocalOptimalEscapeBump
public import DirectedCycles.LocalGleasonBootstrapCore
public import DirectedCycles.LocalRestrictedCostWords
public import DirectedCycles.LocalWordBallBump
public import DirectedCycles.LocalEscapeDerivativeBound
public import DirectedCycles.LocalSubgroupTransport

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

/-- The finite local Gleason product bootstrap with actual local bumps,
convolution and power segments. All products used by the analytic argument
are justified by the 200-letter approximate-group domain. -/
theorem finite_gleason_regularized (hd : L.DivisionClosed) (hr : L.Reversible)
    (A : Finset G) {K : ℕ} (hA : IsLocalFiniteApproximateGroup L K A)
    (S Q : Set G) (hSA : S ⊆ A) (hQ1 : L.one ∈ Q) (hQi : ∀ q ∈ Q, L.inv q ∈ Q)
    (C M N : ℕ) (hC : 0 < C) (hM : 0 < M) (hN : 0 < N)
    (hfirst : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ C → L.PowerIn (L.wordPower (A : Set G) 4) x j) → x ∈ A)
    (hsecond : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ M → L.PowerIn (A : Set G) x j) → x ∈ S)
    (hconj : ∀ h ∈ S, ∀ y ∈ L.wordPower (A : Set G) 3,
      ∃ c ∈ Q, L.Product [L.inv y,h,y] c)
    (hQdom : L.AllProductsDefined Q N) (hQA : L.wordPower Q N ⊆ A)
    (hconstants : 2*(C : ℝ)*(K : ℝ)^2 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ∀ g, L.escapeNorm (A : Set G) g ≤
      (8*(C : ℝ)*(K : ℝ)*(M : ℝ))*L.restrictedEscapeDistance (A : Set G) ε g := by
  classical
  have hc := hd.cancellative L hr
  have hKr : 1 ≤ (K : ℝ) := by exact_mod_cast hA.one_le
  have hK0 : 0 < (K : ℝ) := by linarith
  have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
  have hMr : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hone : ∀ n : ℕ, L.one ∈ L.wordPower (A : Set G) n := by
    intro n
    refine ⟨List.replicate n L.one,List.length_replicate,?_,L.product_replicate_one n⟩
    intro x hx
    exact (List.mem_replicate.mp hx).2.symm ▸ hA.one_mem
  have hS1 : L.one ∈ S := hsecond L.one (fun j _ _ => ⟨L.one,hA.one_mem,L.product_replicate_one j⟩)
  have hsub : ∀ n : ℕ, 1 ≤ n → n ≤ 200 → (A : Set G) ⊆ L.wordPower (A : Set G) n := by
    intro n hn hn'
    simpa only [L.wordPower_one] using L.wordPower_subset_wordPower hA.one_mem hA.allProducts hn hn'
  have hQsub : Q ⊆ A := by
    simpa only [L.wordPower_one] using
      L.wordPower_subset_of_maximum hQ1 hQdom hQA 1 (by omega)
  let R := L.wordPower (A : Set G) 4
  have hRdom : L.AllProductsDefined R 3 := hA.allProducts.wordPower L (by omega : 4*3 ≤ 200)
  have hAdom : L.AllProductsDefined (A : Set G) 3 := hA.allProducts.mono L (Set.Subset.refl _) (by omega)
  have hB : ∀ x ∈ R, ∀ y ∈ R, L.Defined x y := by
    intro x hx y hy
    obtain ⟨z,hz⟩ := hRdom [x,y] (by simp) (by aesop)
    exact ⟨z,(Product.pair_iff L _ _ _).1 hz⟩
  by_cases hproper : ∃ b : G, b ∉ A
  · obtain ⟨r,b,hrε,hb,hbr,hsep,φ,hφ,hφA,hφs,hφlip⟩ :=
      L.exists_optimal_escape_bump hd hr A hA.one_mem hA.inv_mem hAdom hproper hε
    have hrpos : 0 < r := hε.trans_le hrε
    obtain ⟨ψ,hψ,hψA,hψs,hψlip⟩ :=
      L.exists_wordBall_bump hd hr A Q hQ1 hQi N hN hQdom hQA hAdom
    let f := L.normalizedConvolution A φ ψ
    let d := L.restrictedEscapeDistance (A : Set G) ε
    let θ := (C : ℝ)*(K : ℝ)^2/(N : ℝ)
    have hd0 : ∀ g, 0 ≤ d g := L.restrictedEscapeDistance_nonneg hA.one_mem hε.le
    have hθ : 0 ≤ θ := by dsimp [θ]; positivity
    have hθhalf : θ ≤ 1/2 := by
      apply (div_le_iff₀ hNr).2
      nlinarith
    have hf : ‖f‖ ≤ K := L.norm_normalizedConvolution_le hA hφ hψ hφs
    have hf1 : 1 ≤ f L.one := L.normalizedConvolution_one hc A hA.one_mem hA.inv_mem
      (fun x => (hφ x).1) (fun x => (hψ x).1) hφA hψA
    have hfs : ∀ x, x ∉ R → f x = 0 := fun _ hx => L.normalizedConvolution_support hc
      (hA.allProducts.mono L (Set.Subset.refl _) (by omega : 4 ≤ 200)) hφs hψs hx
    have hfR : ∀ x, f x ≠ 0 → x ∈ R := by
      intro x hx
      by_contra hn
      exact hx (hfs x hn)
    have he : ∀ g, L.escapeNorm (A : Set G) g ≤ (C : ℝ)*L.derivativeNorm f g :=
      L.escapeNorm_le_mul_derivativeNorm hc (hone 4) hB C hC hfirst f hf1 hfs
    have hs : ∀ g, L.escapeNorm S g ≤ (M : ℝ)*L.escapeNorm (A : Set G) g :=
      L.escapeNorm_le_mul_of_trapping hA.one_mem M hM hsecond
    have hφd : ∀ g, L.derivativeNorm φ g ≤ d g/r := by
      intro g
      exact (L.derivativeNorm_le_iff _ _ (div_nonneg (hd0 g) hrpos.le)).2 (hφlip g)
    have hψd : ∀ c ∈ Q, L.derivativeNorm ψ c ≤ 1/(N : ℝ) := by
      intro c hcQ
      exact (L.derivativeNorm_le_iff _ _ (by positivity)).2 (hψlip c hcQ)
    have hcomm : ∀ h ∈ S, ∀ y ∈ L.wordPower (A : Set G) 3,
        ∃ c ∈ L.wordPower (A : Set G) 3, ∃ t,
        L.mulRel h y t ∧ L.mulRel y c t ∧ L.derivativeNorm ψ c ≤ 1/(N : ℝ) := by
      intro h hh y hy
      obtain ⟨c,hcQ,hpc⟩ := hconj h hh y hy
      obtain ⟨u,t,hu,ht,hm⟩ := hpc.split_allow_empty L (a := [L.inv y]) (b := [h,y]) rfl
      have heu := (Product.singleton_iff L).1 hu
      subst u
      have hct : L.mulRel y c t := by simpa only [L.inv_inv] using hd.left hm
      exact ⟨c,hsub 3 (by omega) (by omega) (hQsub hcQ),t,
        (Product.pair_iff L _ _ _).1 ht,hct,hψd c hcQ⟩
    have hstart : ∃ X : ℝ, 0 ≤ X ∧ ∀ g, L.derivativeNorm f g ≤ X*d g := by
      refine ⟨2*(K : ℝ)/r,by positivity,?_⟩
      intro g
      by_cases hg : g ∈ A
      · calc
          L.derivativeNorm f g ≤ (K : ℝ)*L.derivativeNorm φ g :=
            L.derivativeNorm_normalizedConvolution_le hc hA hφs hψ hψs hg
          _ ≤ (K : ℝ)*(d g/r) := mul_le_mul_of_nonneg_left (hφd g) hK0.le
          _ ≤ (2*(K : ℝ)/r)*d g := by
            have hh : 0 ≤ (K : ℝ)*(d g/r) := mul_nonneg hK0.le (div_nonneg (hd0 g) hrpos.le)
            calc
              (K : ℝ)*(d g/r) ≤ 2*((K : ℝ)*(d g/r)) := by linarith
              _ = (2*(K : ℝ)/r)*d g := by ring
      · have hrle : r ≤ d g := hsep g hg
        have hdiv : 1 ≤ d g/r := (le_div_iff₀ hrpos).2 (by simpa using hrle)
        calc
          L.derivativeNorm f g ≤ 2*‖f‖ := L.derivativeNorm_le_two_mul f g
          _ ≤ 2*(K : ℝ) := by linarith
          _ ≤ (2*(K : ℝ)/r)*d g := by
            calc
              2*(K : ℝ) ≤ 2*(K : ℝ)*(d g/r) := by
                simpa only [_root_.mul_one] using mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ 2*(K : ℝ))
              _ = (2*(K : ℝ)/r)*d g := by ring
    have hsecond' : ∀ X : ℝ, 0 ≤ X → (∀ g, L.derivativeNorm f g ≤ X*d g) →
        ∀ g ∈ (A : Set G), ∀ h ∈ S,
        L.derivativeNorm (L.derivative g f) h ≤ θ*X*d g := by
      intro X _ hbound g hg h hh
      have hsep' : 1 ≤ (C : ℝ)*X*r := by
        have h1 := he b
        rw [L.escapeNorm_eq_one_of_not_mem hA.one_mem hb] at h1
        have h2 := mul_le_mul_of_nonneg_left (hbound b) hCr.le
        change (C : ℝ)*L.derivativeNorm f b ≤ (C : ℝ)*(X*L.restrictedEscapeDistance (A : Set G) ε b) at h2
        rw [hbr] at h2
        nlinarith
      have hinv : 1/r ≤ (C : ℝ)*X := (div_le_iff₀ hrpos).2 hsep'
      have hφimproved : L.derivativeNorm φ g ≤ (C : ℝ)*X*d g := by
        apply (hφd g).trans
        have hh' := mul_le_mul_of_nonneg_right hinv (hd0 g)
        simpa only [one_div,div_eq_mul_inv,_root_.one_mul,mul_comm,mul_left_comm,mul_assoc] using hh'
      calc
        L.derivativeNorm (L.derivative g f) h ≤ (K : ℝ)^2*L.derivativeNorm φ g*(1/(N : ℝ)) :=
          L.derivativeNorm_twice_normalizedConvolution_le hc hA hφs hψs hg
            (hsub 3 (by omega) (by omega) (hSA hh)) (by positivity) (hcomm h hh)
        _ ≤ (K : ℝ)^2*((C : ℝ)*X*d g)*(1/(N : ℝ)) := by gcongr
        _ = θ*X*d g := by dsimp [θ]; ring
    exact L.gleason_bootstrap_core hc hA.one_mem hS1 (hsub 4 (by omega) (by omega))
      (fun _ h => hsub 4 (by omega) (by omega) (hSA h)) hRdom
      hε hCr.le hKr hMr hθ hθhalf f hfR hf he hs hstart hsecond'
  · have hfull : ∀ x : G, x ∈ (A : Set G) := by simpa using hproper
    have hglobal : L.IsGlobalSubgroup (A : Set G) := {
      one_mem := hA.one_mem
      inv_mem := hA.inv_mem
      mul_total := by
        intro x hx y hy
        obtain ⟨z,hz⟩ := hAdom [x,y] (by simp) (by aesop)
        exact ⟨z,hfull z,(Product.pair_iff L _ _ _).1 hz⟩ }
    intro g
    rw [hglobal.escapeNorm_eq_zero (Set.Subset.refl _) hA.one_mem (hfull g)]
    exact mul_nonneg (by positivity) (L.restrictedEscapeDistance_nonneg hA.one_mem hε.le g)

/-- The resulting bound holds for every fully defined word and contains no
regularization, bump function, or derivative assumption. -/
theorem finite_gleason_product (hd : L.DivisionClosed) (hr : L.Reversible)
    (A : Finset G) {K : ℕ} (hA : IsLocalFiniteApproximateGroup L K A)
    (S Q : Set G) (hSA : S ⊆ A) (hQ1 : L.one ∈ Q) (hQi : ∀ q ∈ Q, L.inv q ∈ Q)
    (C M N : ℕ) (hC : 0 < C) (hM : 0 < M) (hN : 0 < N)
    (hfirst : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ C → L.PowerIn (L.wordPower (A : Set G) 4) x j) → x ∈ A)
    (hsecond : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ M → L.PowerIn (A : Set G) x j) → x ∈ S)
    (hconj : ∀ h ∈ S, ∀ y ∈ L.wordPower (A : Set G) 3,
      ∃ c ∈ Q, L.Product [L.inv y,h,y] c)
    (hQdom : L.AllProductsDefined Q N) (hQA : L.wordPower Q N ⊆ A)
    (hconstants : 2*(C : ℝ)*(K : ℝ)^2 ≤ N)
    {l : List G} {x : G} (hp : L.Product l x) :
    L.escapeNorm (A : Set G) x ≤ (8*(C : ℝ)*(K : ℝ)*(M : ℝ))*(l.map (L.escapeNorm (A : Set G))).sum := by
  apply L.escape_word_bound_of_restricted_regularized hA.one_mem (by positivity) _ hp
  intro ε hε
  exact L.finite_gleason_regularized hd hr A hA S Q hSA hQ1 hQi C M N hC hM hN
    hfirst hsecond hconj hQdom hQA hconstants hε
end LocalGroupAlgebra
end DirectedCycles
