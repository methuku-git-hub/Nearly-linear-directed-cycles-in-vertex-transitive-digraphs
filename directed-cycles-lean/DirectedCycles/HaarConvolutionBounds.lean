module

public import DirectedCycles.HaarGroupConvolution

@[expose] public section

set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant]

omit [μ.IsMulLeftInvariant] in
/-- An integrable first factor and a bounded measurable second factor
supply every convolution integrability obligation. -/
theorem haarConvolution_exists_of_integrable_bounded [MeasurableInv G]
    {f k : G → ℝ} (hf : Integrable f μ) (hk : Measurable k) {C : ℝ}
    (hkb : ∀ x, |k x| ≤ C) : HaarConvolutionExists μ f k := by
  intro x
  exact hf.mul_bdd (hk.comp (measurable_inv.mul_const x)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hkb (y⁻¹*x)))

omit [Group G] [MeasurableMul G] [μ.IsMulLeftInvariant] in
/-- A bounded integrand supported in a finite-measure set has the
explicit measure-times-bound integral estimate. -/
theorem abs_integral_le_support_bound {f : G → ℝ} {A : Set G}
    (hA : μ A ≠ ⊤) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ A, |f x| ≤ C)
    (hs : ∀ x, x ∉ A → f x = 0) : |∫ x, f x ∂μ| ≤ C*μ.real A := by
  have he := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ) hs
  rw [← he]
  have : IsFiniteMeasure (μ.restrict A) := ⟨by simpa using hA.lt_top⟩
  have hball : ∀ x, |f x| ≤ C := by
    intro x
    by_cases hx : x ∈ A
    · exact hbound x hx
    · simpa only [hs x hx,abs_zero] using hC
  simpa only [Real.norm_eq_abs,Measure.restrict_apply_univ,measureReal_def] using
    norm_integral_le_of_norm_le_const (μ := μ.restrict A) (f := f) (C := C)
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hball x))

omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
/-- The first-factor support bounds Haar convolution without an
assumed finite group or a counting-measure normalization. -/
theorem haarConvolution_bound {f k : G → ℝ} {A : Set G} (hA : μ A ≠ ⊤)
    {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hfs : ∀ x, x ∉ A → f x = 0) (hf : ∀ x, |f x| ≤ s) (hk : ∀ x, |k x| ≤ r) (x : G) :
    |haarConvolution μ f k x| ≤ μ.real A*s*r := by
  apply (abs_integral_le_support_bound μ hA (mul_nonneg hs hr) (fun y _ => ?_)
    (fun y hy => by rw [hfs y hy,zero_mul])).trans_eq (by ring)
  rw [abs_mul]
  exact mul_le_mul (hf y) (hk _) (abs_nonneg _) hs

/-- First differentiation preserves the exact convolution existence predicate. -/
theorem HaarConvolutionExists.derivative {f k : G → ℝ}
    (hf : HaarConvolutionExists μ f k) (g : G) :
    HaarConvolutionExists μ (groupDerivative g f) k := by
  intro x
  have h := ((hf.leftShift μ g) x).sub (hf x)
  change Integrable (fun y => DirectedCycles.leftShift g f y*k (y⁻¹*x)-f y*k (y⁻¹*x)) μ at h
  simpa only [groupDerivative,Pi.sub_apply,sub_mul] using h

/-- The mixed second derivative has the exact conjugated integrand
needed in the locally compact Gleason estimates. -/
theorem groupDerivative_twice_haarConvolution {f k : G → ℝ}
    (hf : HaarConvolutionExists μ f k) (g h x : G) :
    groupDerivative h (groupDerivative g (haarConvolution μ f k)) x =
      ∫ y, groupDerivative g f y * groupDerivative (y⁻¹*h*y) k (y⁻¹*x) ∂μ := by
  rw [groupDerivative_haarConvolution μ hf]
  exact groupDerivative_haarConvolution_right μ (hf.derivative μ g) h x

/-- Quantified second-derivative bound with the actual support measure. -/
theorem haarConvolution_second_bound {f k : G → ℝ}
    (hf : HaarConvolutionExists μ f k) (g h : G) {A : Set G} (hA : μ A ≠ ⊤)
    {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hfs : ∀ y, y ∉ A → groupDerivative g f y = 0)
    (hdf : ∀ y, |groupDerivative g f y| ≤ s)
    (hdk : ∀ y ∈ A, ∀ z, |groupDerivative (y⁻¹*h*y) k z| ≤ r) (x : G) :
    |groupDerivative h (groupDerivative g (haarConvolution μ f k)) x| ≤ μ.real A*s*r := by
  rw [groupDerivative_twice_haarConvolution μ hf]
  apply (abs_integral_le_support_bound μ hA (mul_nonneg hs hr) (fun y hy => ?_)
    (fun y hy => by rw [hfs y hy,zero_mul])).trans_eq (by ring)
  rw [abs_mul]
  exact mul_le_mul (hdf y) (hdk y hy _) (abs_nonneg _) hs
omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
/-- The right-factor derivative bound uses the actual support measure
and is uniform in the evaluation point. -/
theorem haarConvolution_first_right_bound {f k : G → ℝ}
    (hf : HaarConvolutionExists μ f k) (g : G) {A : Set G} (hA : μ A ≠ ⊤)
    {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hfs : ∀ y, y ∉ A → f y = 0) (hfb : ∀ y, |f y| ≤ s)
    (hdk : ∀ y ∈ A, ∀ z, |groupDerivative (y⁻¹*g*y) k z| ≤ r) (x : G) :
    |groupDerivative g (haarConvolution μ f k) x| ≤ μ.real A*s*r := by
  rw [groupDerivative_haarConvolution_right μ hf]
  apply (abs_integral_le_support_bound μ hA (mul_nonneg hs hr) (fun y hy => ?_)
    (fun y hy => by rw [hfs y hy,zero_mul])).trans_eq (by ring)
  rw [abs_mul]
  exact mul_le_mul (hfb y) (hdk y hy _) (abs_nonneg _) hs
end DirectedCycles
