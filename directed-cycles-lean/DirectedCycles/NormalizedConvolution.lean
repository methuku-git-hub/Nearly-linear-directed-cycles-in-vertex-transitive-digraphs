import DirectedCycles.FiniteConvolutionBounds
import Mathlib.Combinatorics.Additive.ApproximateSubgroup

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [Fintype G]

noncomputable def normalizedConvolution (A : Finset G) (f k : G → ℝ) : G → ℝ :=
  ((A.card : ℝ)⁻¹) • finiteConvolution f k

theorem normalizedConvolution_one (A : Finset G) (hA : (1 : G) ∈ A)
    (hi : (A : Set G)⁻¹ = A) {f k : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hk : ∀ x, 0 ≤ k x)
    (hfA : ∀ x ∈ A, f x = 1) (hkA : ∀ x ∈ A, k x = 1) :
    1 ≤ normalizedConvolution A f k 1 := by
  have ha : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨1,hA⟩
  change 1 ≤ (A.card : ℝ)⁻¹*finiteConvolution f k 1
  calc
    1 = (A.card : ℝ)⁻¹*A.card := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (finiteConvolution_one_lower A hi hf hk hfA hkA) (by positivity)

theorem normalizedConvolution_support {A : Finset G} {f k : G → ℝ}
    (hf : ∀ x, x ∉ (A : Set G)^2 → f x = 0)
    (hk : ∀ x, x ∉ (A : Set G)^2 → k x = 0)
    {x : G} (hx : x ∉ (A : Set G)^4) : normalizedConvolution A f k x = 0 := by
  have hx' : x ∉ (A : Set G)^2*(A : Set G)^2 := by simpa [← pow_add] using hx
  simp [normalizedConvolution, finiteConvolution_eq_zero hf hk hx']

theorem norm_normalizedConvolution_le {A : Finset G} {K : ℝ}
    (hA : IsApproximateSubgroup K (A : Set G)) {f k : G → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hk : ∀ x, 0 ≤ k x ∧ k x ≤ 1)
    (hfs : ∀ x, x ∉ (A : Set G)^2 → f x = 0) :
    ‖normalizedConvolution A f k‖ ≤ K := by
  classical
  have ha : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨1,hA.one_mem⟩
  have hc : ((A^2).card : ℝ) ≤ K*A.card := by simpa using hA.card_pow_le (n := 2)
  have hs : ∀ x, x ∉ A^2 → f x = 0 := by
    intro x hx
    apply hfs
    simpa only [← Finset.coe_pow, Finset.mem_coe] using hx
  unfold normalizedConvolution
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  calc
    (A.card : ℝ)⁻¹*‖finiteConvolution f k‖ ≤ (A.card : ℝ)⁻¹*(A^2).card :=
      mul_le_mul_of_nonneg_left (norm_finiteConvolution_le_card (A^2) hf hk hs) (by positivity)
    _ ≤ (A.card : ℝ)⁻¹*(K*A.card) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = K := by field_simp

theorem derivativeNorm_normalizedConvolution_le {A : Finset G} {K : ℝ}
    (hA : IsApproximateSubgroup K (A : Set G)) {f k : G → ℝ}
    (hk : ∀ x, 0 ≤ k x ∧ k x ≤ 1)
    (hks : ∀ x, x ∉ (A : Set G)^2 → k x = 0) (g : G) :
    derivativeNorm (normalizedConvolution A f k) g ≤ K*derivativeNorm f g := by
  classical
  have ha : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨1,hA.one_mem⟩
  have hc : ((A^2).card : ℝ) ≤ K*A.card := by simpa using hA.card_pow_le (n := 2)
  have hs : ∀ x, x ∉ A^2 → k x = 0 := by
    intro x hx
    apply hks
    simpa only [← Finset.coe_pow, Finset.mem_coe] using hx
  have hd0 := derivativeNorm_nonneg f g
  unfold normalizedConvolution
  rw [derivativeNorm_smul, abs_of_pos (inv_pos.mpr ha)]
  calc
    _ ≤ (A.card : ℝ)⁻¹ * (derivativeNorm f g * ∑ y : G, k y) :=
      mul_le_mul_of_nonneg_left (derivativeNorm_convolution_le f k g (fun x => (hk x).1)) (by positivity)
    _ ≤ (A.card : ℝ)⁻¹ * (derivativeNorm f g * (A^2).card) := by
      gcongr
      exact sum_le_card_support (A^2) (fun x => (hk x).2) hs
    _ ≤ (A.card : ℝ)⁻¹ * (derivativeNorm f g * (K*A.card)) := by
      gcongr
    _ = K*derivativeNorm f g := by field_simp

/-- The third-power support bound saves one factor of K in the finite global
second-derivative estimate. -/
theorem derivativeNorm_twice_normalizedConvolution_le {A : Finset G} {K : ℝ}
    (hA : IsApproximateSubgroup K (A : Set G)) {f k : G → ℝ}
    (hfs : ∀ x, x ∉ (A : Set G)^2 → f x = 0)
    {g h : G} (hg : g ∈ A) {r : ℝ} (hr : 0 ≤ r)
    (hk : ∀ y ∈ (A : Set G)^3, derivativeNorm k (y⁻¹*h*y) ≤ r) :
    derivativeNorm (groupDerivative g (normalizedConvolution A f k)) h ≤
      K^2*derivativeNorm f g*r := by
  classical
  have ha : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨1,hA.one_mem⟩
  have hc : ((A^3).card : ℝ) ≤ K^2*A.card := by simpa using hA.card_pow_le (n := 3)
  have hs : ∀ y, y ∉ A^3 → groupDerivative g f y = 0 := by
    intro y hy
    apply groupDerivative_support_cube hA.one_mem hfs hg
    simpa only [← Finset.coe_pow, Finset.mem_coe] using hy
  have hk' : ∀ y ∈ A^3, derivativeNorm k (y⁻¹*h*y) ≤ r := by
    intro y hy
    apply hk
    simpa only [← Finset.coe_pow, Finset.mem_coe] using hy
  have hd0 := derivativeNorm_nonneg f g
  unfold normalizedConvolution
  rw [groupDerivative_smul, derivativeNorm_smul, abs_of_pos (inv_pos.mpr ha)]
  calc
    _ ≤ (A.card : ℝ)⁻¹*((A^3).card*derivativeNorm f g*r) :=
      mul_le_mul_of_nonneg_left (derivativeNorm_twice_convolution_le g h (A^3)
        (derivativeNorm_nonneg f g) hr hs le_rfl hk') (by positivity)
    _ ≤ (A.card : ℝ)⁻¹*((K^2*A.card)*derivativeNorm f g*r) := by gcongr
    _ = K^2*derivativeNorm f g*r := by field_simp
end DirectedCycles
