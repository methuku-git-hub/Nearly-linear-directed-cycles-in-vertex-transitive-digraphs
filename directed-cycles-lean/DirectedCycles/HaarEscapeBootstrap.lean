module

public import DirectedCycles.MeasurableEscapeBump
public import DirectedCycles.BoundedGleasonBootstrap
public import DirectedCycles.HaarWordWindowBump
public import DirectedCycles.FiniteConvolutionBounds
public import DirectedCycles.RemoveEscapeRegularization

@[expose] public section

set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
/-- Scalar normalization commutes with actual group differences. -/
theorem groupDerivative_div_constant (f : G → ℝ) (a : ℝ) (g : G) :
    groupDerivative g (fun x => f x/a) = fun x => groupDerivative g f x/a := by
  ext x
  simp only [groupDerivative,leftShift,Pi.sub_apply]
  ring

/-- The Haar version of the complete regularized escape bootstrap.
The bumps, measurability, integrability and derivative bounds are all
constructed from the displayed finite power-trapping data. -/
theorem haar_escape_regularized {U S P : Set G}
    (hU : IsOpen U) (hU1 : (1 : G) ∈ U) (hUi : U⁻¹ = U)
    (hproper : ∃ b : G, b ∉ U) (hP1 : (1 : G) ∈ P) (hPi : P⁻¹ = P)
    (C M N : ℕ) (hC : 0 < C) (hM : 0 < M) (hN : 0 < N)
    (hfirst : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ U^4) → x ∈ U)
    (hsecond : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ M → x^j ∈ U) → x ∈ S)
    (hconj : ∀ h ∈ S, ∀ y ∈ U^3, y⁻¹*h*y ∈ P) (hPN : P^N ⊆ U)
    (hfin2 : μ (U^2) ≠ ⊤) (hfin3 : μ (U^3) ≠ ⊤) (hpos : 0 < μ.real U)
    (hscale : 4*(C : ℝ)*μ.real (U^3) ≤ (N : ℝ)*μ.real U)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ g, escapeNorm U g ≤ (8*(C : ℝ)*(max 1 (μ.real (U^2)/μ.real U))*(M : ℝ))*
      regularizedEscapeDistance U ε g := by
  let K := max 1 (μ.real (U^2)/μ.real U)
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
  have hMr : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hS1 : (1 : G) ∈ S := hsecond 1 (fun _ _ _ => by simpa using hU1)
  obtain ⟨r,b,hrε,hb,hbr,_hsep,φ,hφm,hφ,hφU,hφs,hφlip⟩ :=
    measurable_optimal_escape_bump hU1 hUi hU hproper hε
  have hr : 0 < r := hε.trans_le hrε
  have hφint : Integrable φ μ := by
    have hi : IntegrableOn φ (U^2) μ := Measure.integrableOn_of_bounded hfin2
      hφm.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (hφ x).1]
        exact (hφ x).2))
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
    intro x hx
    by_contra hn
    exact hx (hφs x hn)
  let ψ := wordWindowBump P U N
  have hψ := wordWindowBump_bounds P U hN
  have hψs : ∀ x, x ∉ U^2 → ψ x = 0 := fun _ hx => wordWindowBump_support hP1 hPN hx
  have hc : HaarConvolutionExists μ φ ψ := haarConvolution_exists_of_integrable_bounded μ
    hφint (wordWindowBump_measurable P U hU N)
    (fun x => by rw [abs_of_nonneg (hψ x).1]; exact (hψ x).2)
  let F := haarConvolution μ φ ψ
  let f := fun x => F x/μ.real U
  have hf : ∀ x, |f x| ≤ K := by
    intro x
    have h := haarConvolution_bound μ hfin2 zero_le_one zero_le_one hφs
      (fun y => by rw [abs_of_nonneg (hφ y).1]; exact (hφ y).2)
      (fun y => by rw [abs_of_nonneg (hψ y).1]; exact (hψ y).2) x
    change |F x/μ.real U| ≤ K
    rw [abs_div,abs_of_pos hpos]
    exact (div_le_div_of_nonneg_right (by simpa only [mul_one] using h) hpos.le).trans (le_max_right _ _)
  have hf1 : 1 ≤ f 1 := by
    apply (le_div_iff₀ hpos).2
    simpa only [one_mul] using haarConvolution_plateau_lower μ hU.measurableSet hUi hc
      (fun x => (hφ x).1) (fun x => (hψ x).1) hφU
      (fun _ hx => wordWindowBump_eq_one hP1 hN hx)
  have hfs : ∀ x, x ∉ U^4 → f x = 0 := by
    intro x hx
    have h : F x = 0 := haarConvolution_support μ hφs hψs (by simpa only [← pow_add] using hx)
    change F x/μ.real U = 0
    rw [h,zero_div]
  let d := regularizedEscapeDistance U ε
  have hd : ∀ g, 0 ≤ d g := regularizedEscapeDistance_nonneg hU1 hε.le
  have he : ∀ g, escapeNorm U g ≤ (C : ℝ)*boundedDerivative f g := by
    intro g
    exact (escapeNorm_le_mul_of_trapping (Set.one_mem_pow hU1) C hC hfirst g).trans
      (mul_le_mul_of_nonneg_left (escapeNorm_le_boundedDerivative (Set.one_mem_pow hU1) hf hf1 hfs g) hCr.le)
  have hs : ∀ g, escapeNorm S g ≤ (M : ℝ)*escapeNorm U g :=
    escapeNorm_le_mul_of_trapping hU1 M hM hsecond
  have hstart : ∃ X : ℝ, 0 ≤ X ∧ ∀ g, boundedDerivative f g ≤ X*d g := by
    refine ⟨2*K/ε,by positivity,?_⟩
    intro g
    by_cases hg : g = 1
    · subst g
      rw [boundedDerivative_one]
      exact mul_nonneg (by positivity) (hd 1)
    · have hde : ε ≤ d g := le_wordNorm_of_weight_lower hε.le
        (fun x => le_add_of_nonneg_left (escapeNorm_nonneg hU1 x)) hg
      apply (boundedDerivative_le_two_bound hf g).trans
      have h := mul_le_mul_of_nonneg_left hde (show 0 ≤ 2*K/ε by positivity)
      simpa only [div_mul_cancel₀ _ hε.ne'] using h
  let θ := 2*(C : ℝ)*μ.real (U^3)/((N : ℝ)*μ.real U)
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθhalf : θ ≤ 1/2 := by
    apply (div_le_iff₀ (mul_pos hNr hpos)).2
    nlinarith
  have hsecond' : ∀ X : ℝ, 0 ≤ X → (∀ g, boundedDerivative f g ≤ X*d g) →
      ∀ g ∈ U, ∀ h ∈ S, ∀ x,
        |groupDerivative h (groupDerivative g f) x| ≤ θ*X*d g := by
    intro X hX hbound g hg h hh x
    have hsep : 1 ≤ 2*(C : ℝ)*X*r := by
      have h1 := he b
      rw [escapeNorm_eq_one_of_not_mem hU1 hb] at h1
      have h2 := mul_le_mul_of_nonneg_left (hbound b) hCr.le
      have h3 := mul_le_mul_of_nonneg_left hbr.le (mul_nonneg hCr.le hX)
      change regularizedEscapeDistance U ε b < 2*r at hbr
      change (C : ℝ)*boundedDerivative f b ≤ (C : ℝ)*(X*regularizedEscapeDistance U ε b) at h2
      nlinarith
    have hinv : 1/r ≤ 2*(C : ℝ)*X := (div_le_iff₀ hr).2 hsep
    have hφd : ∀ y, |groupDerivative g φ y| ≤ 2*(C : ℝ)*X*d g := by
      intro y
      apply (hφlip g y).trans
      have h := mul_le_mul_of_nonneg_right hinv (hd g)
      simpa only [d,one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm,mul_left_comm,mul_assoc] using h
    have hφ0 : 0 ≤ 2*(C : ℝ)*X*d g :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCr.le) hX) (hd g)
    have hsecondF := haarConvolution_second_bound μ hc g h hfin3 hφ0
      (by positivity : (0 : ℝ) ≤ 1/(N : ℝ))
      (fun y hy => groupDerivative_support_cube hU1 hφs hg hy) hφd
      (fun y hy z => wordWindowBump_derivative hPi (hconj h hh y hy) hN z) x
    change |groupDerivative h (groupDerivative g (fun y => F y/μ.real U)) x| ≤ _
    rw [groupDerivative_div_constant,groupDerivative_div_constant,abs_div,abs_of_pos hpos]
    apply (div_le_div_of_nonneg_right hsecondF hpos.le).trans_eq
    dsimp [θ]
    ring
  exact bounded_gleason_bootstrap_core hU1 hS1 hε hCr.le hK hMr hθ hθhalf
    f hf he hs hstart hsecond'
end DirectedCycles
