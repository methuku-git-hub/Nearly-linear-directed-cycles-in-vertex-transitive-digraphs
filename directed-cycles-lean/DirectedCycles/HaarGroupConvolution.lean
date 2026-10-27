module

public import DirectedCycles.FiniteGroupDerivatives
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant]

/-- Multiplicative convolution of real functions with the actual left
Haar measure; the group need not be finite or commutative. -/
noncomputable def haarConvolution (f k : G → ℝ) : G → ℝ :=
  fun x => ∫ y, f y * k (y⁻¹*x) ∂μ

/-- The pointwise integrability needed for the algebra of convolution. -/
def HaarConvolutionExists (f k : G → ℝ) : Prop :=
  ∀ x : G, Integrable (fun y => f y * k (y⁻¹*x)) μ

/-- Haar translation gives the first-factor translation identity. -/
theorem haarConvolution_leftShift (g : G) (f k : G → ℝ) :
    haarConvolution μ (leftShift g f) k = leftShift g (haarConvolution μ f k) := by
  funext x
  change (∫ y, f (g⁻¹*y)*k (y⁻¹*x) ∂μ) = ∫ y, f y*k (y⁻¹*(g⁻¹*x)) ∂μ
  have h := integral_mul_left_eq_self (μ := μ) (fun y => f (g⁻¹*y)*k (y⁻¹*x)) g
  simpa only [inv_mul_cancel_left,mul_inv_rev,mul_assoc] using h.symm

omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
/-- Differences may be moved through the Bochner integral when both
original convolution integrands are integrable. -/
theorem haarConvolution_sub_left {f h k : G → ℝ}
    (hf : HaarConvolutionExists μ f k) (hh : HaarConvolutionExists μ h k) :
    haarConvolution μ (f-h) k = haarConvolution μ f k-haarConvolution μ h k := by
  funext x
  simp only [haarConvolution,Pi.sub_apply,sub_mul]
  exact integral_sub (hf x) (hh x)

/-- Translating the first factor preserves the required integrability. -/
theorem HaarConvolutionExists.leftShift {f k : G → ℝ}
    (hf : HaarConvolutionExists μ f k) (g : G) :
    HaarConvolutionExists μ (leftShift g f) k := by
  intro x
  have h := (hf (g⁻¹*x)).comp_mul_left g⁻¹
  simpa only [DirectedCycles.leftShift,mul_inv_rev,inv_inv,mul_assoc,mul_inv_cancel_left] using h

/-- Differentiation of the first convolution factor is valid for Haar
integration, with its integrability supplied by translation invariance. -/
theorem groupDerivative_haarConvolution {f k : G → ℝ}
    (hf : HaarConvolutionExists μ f k) (g : G) :
    groupDerivative g (haarConvolution μ f k) = haarConvolution μ (groupDerivative g f) k := by
  unfold groupDerivative
  rw [haarConvolution_sub_left μ (hf.leftShift μ g) hf,haarConvolution_leftShift]

omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
/-- The conjugation appearing when differentiating the second factor
is exact in an arbitrary group. -/
theorem groupDerivative_haarConvolution_right {f k : G → ℝ}
    (hf : HaarConvolutionExists μ f k) (g x : G) :
    groupDerivative g (haarConvolution μ f k) x =
      ∫ y, f y*groupDerivative (y⁻¹*g*y) k (y⁻¹*x) ∂μ := by
  simp only [groupDerivative,leftShift,Pi.sub_apply,haarConvolution]
  rw [← integral_sub (hf (g⁻¹*x)) (hf x)]
  congr 1
  funext y
  simp only [mul_inv_rev,inv_inv,mul_assoc,mul_inv_cancel_left]
  ring

omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
/-- Support containment holds without an integrability premise. -/
theorem haarConvolution_support {f k : G → ℝ} {A B : Set G}
    (hf : ∀ x, x ∉ A → f x = 0) (hk : ∀ x, x ∉ B → k x = 0)
    {x : G} (hx : x ∉ A*B) : haarConvolution μ f k x = 0 := by
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro y
  change f y * k (y⁻¹*x) = 0
  by_cases hy : y ∈ A
  · have hy' : y⁻¹*x ∉ B := by
      intro h
      exact hx ⟨y,hy,y⁻¹*x,h,by simp⟩
    rw [hk _ hy',mul_zero]
  · rw [hf _ hy,zero_mul]
end DirectedCycles
