import DirectedCycles.HaarEscapeBootstrap

set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [μ.IsMulLeftInvariant] in
/-- A bounded measurable bump supported in a finite-measure square is integrable. -/
theorem bounded_square_bump_integrable {U : Set G} {φ : G → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hφs : ∀ x, x ∉ U^2 → φ x = 0) (hfin : μ (U^2) ≠ ⊤) : Integrable φ μ := by
  have hi : IntegrableOn φ (U^2) μ := Measure.integrableOn_of_bounded hfin
    hφm.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hφ x).1]
      exact (hφ x).2))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro x hx
  by_contra hn
  exact hx (hφs x hn)

omit [μ.IsMulLeftInvariant] in
/-- Normalized self-convolution of a concrete measurable plateau bump
is bounded, is at least one at the identity, and has fourth-power support. -/
theorem haar_normalized_bump {U : Set G} (hU : IsOpen U) (hUi : U⁻¹ = U)
    {φ : G → ℝ} (hφm : Measurable φ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hφU : ∀ x ∈ U, φ x = 1) (hφs : ∀ x, x ∉ U^2 → φ x = 0)
    (hfin : μ (U^2) ≠ ⊤) (hpos : 0 < μ.real U) :
    HaarConvolutionExists μ φ φ ∧
      (∀ x, |haarConvolution μ φ φ x/μ.real U| ≤ μ.real (U^2)/μ.real U) ∧
      1 ≤ haarConvolution μ φ φ 1/μ.real U ∧
      ∀ x, x ∉ U^4 → haarConvolution μ φ φ x/μ.real U = 0 := by
  have hc : HaarConvolutionExists μ φ φ := haarConvolution_exists_of_integrable_bounded μ
    (bounded_square_bump_integrable μ hφm hφ hφs hfin) hφm
    (fun x => by rw [abs_of_nonneg (hφ x).1]; exact (hφ x).2)
  refine ⟨hc,?_,?_,?_⟩
  · intro x
    rw [abs_div,abs_of_pos hpos]
    apply div_le_div_of_nonneg_right _ hpos.le
    simpa only [mul_one] using haarConvolution_bound μ hfin zero_le_one zero_le_one hφs
      (fun y => by rw [abs_of_nonneg (hφ y).1]; exact (hφ y).2)
      (fun y => by rw [abs_of_nonneg (hφ y).1]; exact (hφ y).2) x
  · apply (le_div_iff₀ hpos).2
    simpa only [one_mul] using haarConvolution_plateau_lower μ hU.measurableSet hUi hc
      (fun x => (hφ x).1) (fun x => (hφ x).1) hφU hφU
  · intro x hx
    rw [haarConvolution_support μ hφs hφs (by simpa only [← pow_add] using hx),zero_div]
end DirectedCycles
