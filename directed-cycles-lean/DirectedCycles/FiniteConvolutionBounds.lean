import DirectedCycles.FiniteGroupConvolution
import Mathlib.Analysis.Normed.Module.Basic

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
theorem groupDerivative_smul (f : G → ℝ) (g : G) (c : ℝ) :
    groupDerivative g (c • f) = c • groupDerivative g f := by
  ext x
  simp [groupDerivative, leftShift, mul_sub]

theorem derivativeNorm_smul (f : G → ℝ) (g : G) (c : ℝ) :
    derivativeNorm (c • f) g = |c| * derivativeNorm f g := by
  unfold derivativeNorm
  rw [groupDerivative_smul, norm_smul, Real.norm_eq_abs]

theorem finiteConvolution_one_lower (A : Finset G) (hi : (A : Set G)⁻¹ = A)
    {f k : G → ℝ} (hf : ∀ x, 0 ≤ f x) (hk : ∀ x, 0 ≤ k x)
    (hfA : ∀ x ∈ A, f x = 1) (hkA : ∀ x ∈ A, k x = 1) :
    (A.card : ℝ) ≤ finiteConvolution f k 1 := by
  classical
  have he : (A.card : ℝ) = ∑ x ∈ A, f x*k (x⁻¹*1) := by
    have hterm : ∀ x ∈ A, f x*k (x⁻¹*1) = 1 := by
      intro x hx
      have hxi : x⁻¹ ∈ A := by
        have hh : x⁻¹ ∈ (A : Set G)⁻¹ := Set.inv_mem_inv.mpr hx
        simpa only [hi, Finset.mem_coe] using hh
      simp [hfA x hx, hkA x⁻¹ hxi]
    simp_rw [Finset.sum_congr rfl hterm]
    simp
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
  intro x _ _
  exact mul_nonneg (hf x) (hk _)

theorem norm_finiteConvolution_le_card (A : Finset G) {f k : G → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hk : ∀ x, 0 ≤ k x ∧ k x ≤ 1)
    (hfs : ∀ x, x ∉ A → f x = 0) : ‖finiteConvolution f k‖ ≤ A.card := by
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).2
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (finiteConvolution_nonneg (fun x => (hf x).1)
    (fun x => (hk x).1) x)]
  exact finiteConvolution_le_card A hf hk hfs x

/-- Summation over the second factor is independent of the evaluation point. -/
theorem sum_inv_mul (k : G → ℝ) (x : G) : (∑ y : G, k (y⁻¹*x)) = ∑ y : G, k y := by
  apply Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x))
  intro y
  rfl

theorem derivativeNorm_convolution_le (f k : G → ℝ) (g : G)
    (hk : ∀ x, 0 ≤ k x) :
    derivativeNorm (finiteConvolution f k) g ≤ derivativeNorm f g * ∑ y : G, k y := by
  have hsum : 0 ≤ ∑ y : G, k y := Finset.sum_nonneg (fun y _ => hk y)
  apply (derivativeNorm_le_iff _ _ (mul_nonneg (derivativeNorm_nonneg f g) hsum)).2
  intro x
  rw [groupDerivative_finiteConvolution]
  change |∑ y : G, groupDerivative g f y*k (y⁻¹*x)| ≤ _
  calc
    |∑ y : G, groupDerivative g f y*k (y⁻¹*x)| ≤
        ∑ y : G, |groupDerivative g f y*k (y⁻¹*x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y : G, derivativeNorm f g * k (y⁻¹*x) := by
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul, abs_of_nonneg (hk _)]
      exact mul_le_mul_of_nonneg_right (abs_groupDerivative_le f g y) (hk _)
    _ = derivativeNorm f g * ∑ y : G, k y := by rw [← Finset.mul_sum, sum_inv_mul]

omit [Group G] in
theorem sum_le_card_support (A : Finset G) {k : G → ℝ} (hk : ∀ x, k x ≤ 1)
    (hks : ∀ x, x ∉ A → k x = 0) : (∑ x : G, k x) ≤ A.card := by
  classical
  have he : (∑ x : G, k x) = ∑ x ∈ A, k x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ A)
    intro x _ hx
    exact hks x hx
  rw [he]
  exact (Finset.sum_le_sum (fun x (_ : x ∈ A) => hk x)).trans_eq (by simp)

omit [Fintype G] in
/-- The sharp support containment used in the finite global bootstrap. -/
theorem groupDerivative_support_cube {A : Set G} (hA : 1 ∈ A) {f : G → ℝ}
    (hfs : ∀ x, x ∉ A^2 → f x = 0) {g : G} (hg : g ∈ A)
    {x : G} (hx : x ∉ A^3) : groupDerivative g f x = 0 := by
  have hxs : x ∉ A^2 := fun h => hx ((Set.pow_subset_pow_right hA (by omega : 2 ≤ 3)) h)
  have hxg : g⁻¹*x ∉ A^2 := by
    intro h
    apply hx
    have hh : g*(g⁻¹*x) ∈ A*A^2 := Set.mul_mem_mul hg h
    simpa [← pow_succ'] using hh
  simp [groupDerivative, leftShift, hfs x hxs, hfs (g⁻¹*x) hxg]
end DirectedCycles
