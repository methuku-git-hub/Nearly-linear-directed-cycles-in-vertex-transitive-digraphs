import DirectedCycles.MeasurableWordWindowBump
import DirectedCycles.HaarConvolutionBounds

set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

/-- The constructed word-window bump is integrable whenever its
second-power support has finite Haar measure. -/
theorem wordWindowBump_integrable {Q U : Set G} (hQ : (1 : G) ∈ Q) (hU : IsOpen U)
    {N : ℕ} (hN : 0 < N) (hQU : Q^N ⊆ U) (hfinite : μ (U^2) ≠ ⊤) :
    Integrable (wordWindowBump Q U N) μ := by
  have hm := wordWindowBump_measurable Q U hU N
  have hi : IntegrableOn (wordWindowBump Q U N) (U^2) μ :=
    Measure.integrableOn_of_bounded hfinite hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (wordWindowBump_bounds Q U hN x).1]
        exact (wordWindowBump_bounds Q U hN x).2))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro x hx
  by_contra hn
  exact hx (wordWindowBump_support hQ hQU hn)

/-- Two actual measurable word-window bumps have everywhere integrable
convolution. All analytic premises are supplied by their construction. -/
theorem wordWindowBump_convolution_exists {Q P U : Set G}
    (hQ : (1 : G) ∈ Q) (hU : IsOpen U) {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hQU : Q^N ⊆ U) (hfinite : μ (U^2) ≠ ⊤) :
    HaarConvolutionExists μ (wordWindowBump Q U N) (wordWindowBump P U M) := by
  apply haarConvolution_exists_of_integrable_bounded μ
    (wordWindowBump_integrable μ hQ hU hN hQU hfinite)
    (wordWindowBump_measurable P U hU M)
  intro x
  rw [abs_of_nonneg (wordWindowBump_bounds P U hM x).1]
  exact (wordWindowBump_bounds P U hM x).2

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
/-- Haar convolution is at least the measure of a common symmetric
plateau at the identity. This provides the required nonzero normalization. -/
theorem haarConvolution_plateau_lower {U : Set G} (hU : MeasurableSet U) (hi : U⁻¹ = U)
    {f k : G → ℝ} (hc : HaarConvolutionExists μ f k)
    (hf : ∀ x, 0 ≤ f x) (hk : ∀ x, 0 ≤ k x)
    (hfU : ∀ x ∈ U, f x = 1) (hkU : ∀ x ∈ U, k x = 1) :
    μ.real U ≤ haarConvolution μ f k 1 := by
  have hpoint : ∀ x : G, U.indicator (fun _ => (1 : ℝ)) x ≤ f x*k (x⁻¹*1) := by
    intro x
    by_cases hx : x ∈ U
    · have hxi : x⁻¹ ∈ U := by simpa only [hi] using Set.inv_mem_inv.mpr hx
      simp only [Set.indicator_of_mem hx,mul_one,hfU x hx,hkU x⁻¹ hxi,le_refl]
    · rw [Set.indicator_of_notMem hx]
      exact mul_nonneg (hf x) (hk _)
  have h := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x => (one_indicator_bounds U x).1))
    (hc 1) (Filter.Eventually.of_forall hpoint)
  simpa only [integral_indicator hU,integral_const,smul_eq_mul,mul_one,
    Measure.restrict_apply_univ,measureReal_def,haarConvolution] using h
end DirectedCycles
