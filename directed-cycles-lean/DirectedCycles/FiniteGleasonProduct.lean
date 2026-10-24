import DirectedCycles.NormalizedConvolution
import DirectedCycles.OptimalEscapeBump
import DirectedCycles.GleasonBootstrapCore
import DirectedCycles.RemoveEscapeRegularization
import DirectedCycles.WordBallBump

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [Fintype G]

/-- The finite global Gleason product bootstrap with explicit, consistent
trapping radii. Both bumps and every derivative estimate are constructed here. -/
theorem finite_gleason_regularized (A : Finset G) {K : ℝ}
    (hK : 1 ≤ K) (hA : IsApproximateSubgroup K (A : Set G))
    (S Q : Set G) (hQ : 1 ∈ Q) (hQi : Q⁻¹ = Q)
    (C M N : ℕ) (hC : 0 < C) (hM : 0 < M) (hN : 0 < N)
    (hfirst : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ (A : Set G)^4) → x ∈ A)
    (hsecond : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ M → x^j ∈ A) → x ∈ S)
    (hconj : ∀ h ∈ S, ∀ y ∈ (A : Set G)^3, y⁻¹*h*y ∈ Q)
    (hQA : Q^N ⊆ A) (hconstants : 2*(C : ℝ)*K^2 ≤ N)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ g, escapeNorm (A : Set G) g ≤ (8*(C : ℝ)*K*(M : ℝ))*regularizedEscapeDistance (A : Set G) ε g := by
  classical
  have hK0 : 0 < K := by linarith
  have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
  have hMr : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hS : 1 ∈ S := hsecond 1 (fun _ _ _ => by simpa using hA.one_mem)
  have hA4 : (1 : G) ∈ (A : Set G)^4 := Set.one_mem_pow hA.one_mem
  by_cases hproper : ∃ b : G, b ∉ A
  · obtain ⟨r,b,hrε,hb,hbr,_,φ,hφ,hφA,hφs,hφlip⟩ :=
      exists_optimal_escape_bump A hA.one_mem hA.inv_eq_self hproper hε
    have hr : 0 < r := hε.trans_le hrε
    obtain ⟨ψ,hψ,hψA,hψs,hψlip⟩ :=
      exists_wordBall_bump A hA.one_mem Q hQ hQi (by omega) hQA
    let f := normalizedConvolution A φ ψ
    let d := regularizedEscapeDistance (A : Set G) ε
    let θ := (C : ℝ)*K^2/(N : ℝ)
    have hd : ∀ g, 0 ≤ d g := regularizedEscapeDistance_nonneg hA.one_mem hε.le
    have hθ : 0 ≤ θ := by dsimp [θ]; positivity
    have hθhalf : θ ≤ 1/2 := by
      apply (div_le_iff₀ hNr).2
      nlinarith
    have hf : ‖f‖ ≤ K := norm_normalizedConvolution_le hA hφ hψ hφs
    have hf1 : 1 ≤ f 1 := normalizedConvolution_one A hA.one_mem hA.inv_eq_self
      (fun x => (hφ x).1) (fun x => (hψ x).1) hφA hψA
    have hfs : ∀ x, x ∉ (A : Set G)^4 → f x = 0 :=
      fun _ hx => normalizedConvolution_support hφs hψs hx
    have he : ∀ g, escapeNorm (A : Set G) g ≤ (C : ℝ)*derivativeNorm f g :=
      escapeNorm_le_mul_derivativeNorm hA4 C hC hfirst f hf1 hfs
    have hs : ∀ g, escapeNorm S g ≤ (M : ℝ)*escapeNorm (A : Set G) g :=
      escapeNorm_le_mul_of_trapping hA.one_mem M hM hsecond
    have hφd : ∀ g, derivativeNorm φ g ≤ d g/r := by
      intro g
      apply (derivativeNorm_le_iff _ _ (div_nonneg (hd g) hr.le)).2
      intro x
      exact hφlip g x
    have hψd : ∀ h ∈ S, ∀ y ∈ (A : Set G)^3,
        derivativeNorm ψ (y⁻¹*h*y) ≤ 1/(N : ℝ) := by
      intro h hh y hy
      apply (derivativeNorm_le_iff _ _ (by positivity)).2
      intro x
      exact hψlip _ (hconj h hh y hy) x
    have hstart : ∃ X : ℝ, 0 ≤ X ∧ ∀ g, derivativeNorm f g ≤ X*d g := by
      refine ⟨K/r,by positivity,?_⟩
      intro g
      calc
        derivativeNorm f g ≤ K*derivativeNorm φ g := derivativeNorm_normalizedConvolution_le hA hψ hψs g
        _ ≤ K*(d g/r) := mul_le_mul_of_nonneg_left (hφd g) hK0.le
        _ = (K/r)*d g := by ring
    have hsecond' : ∀ X : ℝ, 0 ≤ X → (∀ g, derivativeNorm f g ≤ X*d g) →
        ∀ g ∈ (A : Set G), ∀ h ∈ S,
        derivativeNorm (groupDerivative g f) h ≤ θ*X*d g := by
      intro X hX hbound g hg h hh
      have hsep : 1 ≤ (C : ℝ)*X*r := by
        have h1 := he b
        rw [escapeNorm_eq_one_of_not_mem hA.one_mem hb] at h1
        have h2 := mul_le_mul_of_nonneg_left (hbound b) hCr.le
        change (C : ℝ)*derivativeNorm f b ≤ (C : ℝ)*(X*regularizedEscapeDistance (A : Set G) ε b) at h2
        rw [hbr] at h2
        nlinarith
      have hinv : 1/r ≤ (C : ℝ)*X := (div_le_iff₀ hr).2 hsep
      have hφimproved : derivativeNorm φ g ≤ (C : ℝ)*X*d g := by
        apply (hφd g).trans
        have hh' := mul_le_mul_of_nonneg_right hinv (hd g)
        simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc] using hh'
      calc
        derivativeNorm (groupDerivative g f) h ≤ K^2*derivativeNorm φ g*(1/(N : ℝ)) :=
          derivativeNorm_twice_normalizedConvolution_le hA hφs hg (by positivity) (hψd h hh)
        _ ≤ K^2*((C : ℝ)*X*d g)*(1/(N : ℝ)) := by
          gcongr
        _ = θ*X*d g := by dsimp [θ]; ring
    exact gleason_bootstrap_core hA.one_mem hS hε hCr.le hK hMr hθ hθhalf
      f hf he hs hstart hsecond'
  · intro g
    have hfull : ∀ x : G, x ∈ (A : Set G) := by simpa using hproper
    rw [(escapeNorm_eq_zero_iff hA.one_mem g).2 (fun n => hfull (g^n))]
    exact mul_nonneg (by positivity) (regularizedEscapeDistance_nonneg hA.one_mem hε.le g)

/-- The finite global product estimate, with no regularization or analytic input
left unproved. Existence of strong trapping data remains a separate theorem. -/
theorem finite_gleason_product (A : Finset G) {K : ℝ}
    (hK : 1 ≤ K) (hA : IsApproximateSubgroup K (A : Set G))
    (S Q : Set G) (hQ : 1 ∈ Q) (hQi : Q⁻¹ = Q)
    (C M N : ℕ) (hC : 0 < C) (hM : 0 < M) (hN : 0 < N)
    (hfirst : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ (A : Set G)^4) → x ∈ A)
    (hsecond : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ M → x^j ∈ A) → x ∈ S)
    (hconj : ∀ h ∈ S, ∀ y ∈ (A : Set G)^3, y⁻¹*h*y ∈ Q)
    (hQA : Q^N ⊆ A) (hconstants : 2*(C : ℝ)*K^2 ≤ N)
    (l : List G) :
    escapeNorm (A : Set G) l.prod ≤ (8*(C : ℝ)*K*(M : ℝ))*(l.map (escapeNorm (A : Set G))).sum := by
  have hK0 : 0 ≤ K := by linarith
  apply escape_product_bound_of_regularized hA.one_mem (by positivity)
  intro ε hε
  exact finite_gleason_regularized A hK hA S Q hQ hQi C M N hC hM hN
    hfirst hsecond hconj hQA hconstants hε
end DirectedCycles
