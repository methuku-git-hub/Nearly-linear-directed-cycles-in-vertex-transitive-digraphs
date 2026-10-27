module

public import DirectedCycles.CompactNSSCurve
public import DirectedCycles.CentralLiftRounding

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {H : Type*} [Group H]

theorem real_curve_neg (φ : ℝ → H) (h0 : φ 0 = 1)
    (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (t : ℝ) : φ (-t) = (φ t)⁻¹ := by
  apply mul_left_cancel (a := φ t)
  rw [← hadd,add_neg_cancel,h0,mul_inv_cancel]

theorem real_curve_sub (φ : ℝ → H) (h0 : φ 0 = 1)
    (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (s t : ℝ) : φ (s-t) = φ s*(φ t)⁻¹ := by
  rw [sub_eq_add_neg,hadd,real_curve_neg φ h0 hadd]

theorem real_curve_int_mul (φ : ℝ → H) (h0 : φ 0 = 1)
    (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (t : ℝ) (m : ℤ) : φ ((m : ℝ)*t) = (φ t)^m := by
  rcases Int.eq_nat_or_neg m with ⟨n,rfl|rfl⟩
  · simpa only [Int.cast_natCast,zpow_natCast] using real_additive_curve_nat_mul φ h0 hadd t n
  · simp only [Int.cast_neg,Int.cast_natCast,neg_mul,real_curve_neg φ h0 hadd,
      real_additive_curve_nat_mul φ h0 hadd,zpow_neg,zpow_natCast]

/-- A nontrivial one-parameter curve with its radius-R segment in an NSS
region has no nonzero period of absolute value at most 2R. Integer rounding
reduces any putative periodic curve into that segment, forcing triviality. -/
theorem real_curve_kernel_gap (φ : ℝ → H) (h0 : φ 0 = 1)
    (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (h1 : φ 1 ≠ 1)
    (V : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (R : ℝ) (hbound : ∀ t : ℝ, |t| ≤ R → φ t ∈ V)
    {t : ℝ} (htpos : 0 < |t|) (htbound : |t| ≤ 2*R) : φ t ≠ 1 := by
  intro ht
  have hperiod : φ |t| = 1 := by
    rcases le_or_gt 0 t with h | h
    · simpa only [abs_of_nonneg h] using ht
    · rw [abs_of_neg h,real_curve_neg φ h0 hadd,ht,inv_one]
  have hall : ∀ s : ℝ, φ s ∈ V := by
    intro s
    obtain ⟨m,hm⟩ := exists_nearest_scaled_integer s htpos
    have hmul : φ ((m : ℝ)*|t|) = 1 := by rw [real_curve_int_mul φ h0 hadd,hperiod,one_zpow]
    have hres : φ (s-(m : ℝ)*|t|) = φ s := by rw [real_curve_sub φ h0 hadd,hmul,inv_one,mul_one]
    rw [← hres]
    exact hbound _ (hm.trans (by linarith))
  apply h1
  apply hNSS
  intro n
  have he := real_additive_curve_nat_mul φ h0 hadd 1 n
  have he' : φ (n : ℝ) = (φ 1)^n := by simpa only [mul_one] using he
  rw [← he']
  exact hall (n : ℝ)
end DirectedCycles
