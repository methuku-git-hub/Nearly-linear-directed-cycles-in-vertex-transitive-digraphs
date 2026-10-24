import DirectedCycles.HaarWordWindowBump
import DirectedCycles.PointwiseGroupDerivative
import DirectedCycles.FiniteConvolutionBounds

set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]

/-- The analytic finite-trapping step, using two explicitly constructed
measurable bumps and Haar convolution. Every derivative and integrability
condition is derived here from the displayed finite-word inclusions. -/
theorem haar_finite_trapping_core {Q P U V : Set G}
    (hQ1 : (1 : G) ∈ Q) (hP1 : (1 : G) ∈ P) (hU1 : (1 : G) ∈ U)
    (hQi : Q⁻¹ = Q) (hPi : P⁻¹ = P) (hUi : U⁻¹ = U) (hU : IsOpen U)
    {n M m : ℕ} (hn : 0 < n) (hM : 0 < M)
    (hQn : Q^n ⊆ U) (hPM : P^M ⊆ U)
    (hcyclic : ∀ q ∈ Q, ∀ j : ℕ, q^j ∈ V)
    (hconj : ∀ v ∈ V, ∀ y ∈ U^3, y⁻¹*v*y ∈ P)
    (hfinite2 : μ (U^2) ≠ ⊤) (hfinite3 : μ (U^3) ≠ ⊤)
    (hscale : (m : ℝ)*(μ.real (U^2)+μ.real (U^3)) < (M : ℝ)*μ.real U) :
    Q^(m*n) ⊆ U^4 := by
  let f := wordWindowBump Q U n
  let k := wordWindowBump P U M
  let φ := haarConvolution μ f k
  have hf := wordWindowBump_bounds Q U hn
  have hk := wordWindowBump_bounds P U hM
  have hfs : ∀ x, x ∉ U^2 → f x = 0 := fun _ hx => wordWindowBump_support hQ1 hQn hx
  have hks : ∀ x, x ∉ U^2 → k x = 0 := fun _ hx => wordWindowBump_support hP1 hPM hx
  have hc : HaarConvolutionExists μ f k :=
    wordWindowBump_convolution_exists μ hQ1 hU hn hM hQn hfinite2
  have hφ1 : μ.real U ≤ φ 1 := haarConvolution_plateau_lower μ hU.measurableSet hUi hc
    (fun x => (hf x).1) (fun x => (hk x).1)
    (fun _ hx => wordWindowBump_eq_one hQ1 hn hx)
    (fun _ hx => wordWindowBump_eq_one hP1 hM hx)
  have hφs : ∀ x, x ∉ U^4 → φ x = 0 := by
    intro x hx
    exact haarConvolution_support μ hfs hks (by simpa only [← pow_add] using hx)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hqU : Q ⊆ U := by
    have h := Set.pow_subset_pow_right hQ1 (show 1 ≤ n by omega)
    simpa only [pow_one] using h.trans hQn
  have hdk : ∀ v ∈ V, ∀ y ∈ U^3, ∀ x, |groupDerivative (y⁻¹*v*y) k x| ≤ 1/(M : ℝ) := by
    intro v hv y hy x
    exact wordWindowBump_derivative hPi (hconj v hv y hy) hM x
  have hdf : ∀ q ∈ Q, ∀ x, |groupDerivative q f x| ≤ 1/(n : ℝ) := by
    intro q hq x
    exact wordWindowBump_derivative hQi hq hn x
  have hsmall : ∀ q ∈ Q, ∀ x,
      |groupDerivative q φ x| ≤ (μ.real (U^2)+μ.real (U^3))/((n : ℝ)*M) := by
    intro q hq x
    have hpow : ∀ z, |groupDerivative (q^n) φ z| ≤ μ.real (U^2)/(M : ℝ) := by
      intro z
      have h := haarConvolution_first_right_bound μ hc (q^n) hfinite2 zero_le_one
        (by positivity : (0 : ℝ) ≤ 1/(M : ℝ)) hfs
        (fun y => by rw [abs_of_nonneg (hf y).1]; exact (hf y).2)
        (fun y hy => hdk (q^n) (hcyclic q hq n) y
          (Set.pow_subset_pow_right hU1 (by omega : 2 ≤ 3) hy)) z
      simpa only [mul_one,div_eq_mul_inv,one_mul] using h
    have hsecond : ∀ i < n, ∀ z,
        |groupDerivative (q^i) (groupDerivative q φ) z| ≤ μ.real (U^3)/(n : ℝ)/(M : ℝ) := by
      intro i _ z
      have h := haarConvolution_second_bound μ hc q (q^i) hfinite3
        (by positivity : (0 : ℝ) ≤ 1/(n : ℝ)) (by positivity : (0 : ℝ) ≤ 1/(M : ℝ))
        (fun y hy => groupDerivative_support_cube hU1 hfs (hqU hq) hy)
        (hdf q hq) (hdk (q^i) (hcyclic q hq i)) z
      simpa only [div_eq_mul_inv,one_mul] using h
    have h := groupDerivative_taylor_pointwise φ q hn hpow hsecond x
    convert h using 1
    field_simp
  intro g hg
  apply groupDerivative_support_detection hφ1 hφs
  intro x
  have h := groupDerivative_word_bound hsmall (m*n) g hg x
  have he : ((m*n : ℕ) : ℝ)*((μ.real (U^2)+μ.real (U^3))/((n : ℝ)*M)) =
      (m : ℝ)*(μ.real (U^2)+μ.real (U^3))/(M : ℝ) := by
    push_cast
    field_simp
  rw [he] at h
  exact h.trans_lt ((div_lt_iff₀ hMR).mpr (by simpa only [mul_comm] using hscale))
end DirectedCycles
