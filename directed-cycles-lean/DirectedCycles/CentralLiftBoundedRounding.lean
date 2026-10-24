import DirectedCycles.CentralLiftRounding

set_option autoImplicit false
namespace DirectedCycles

/-- Rounding the actual scaled coordinate also bounds the signed correction
exponent. These bounds keep every corrected power inside a doubled certified
segment, including when the coordinate has negative sign. -/
theorem central_lift_bounded_rounding {δ t t' M₀ M₁ : ℝ}
    (hδ : 0 < δ) (ht : |t| ≤ (11/10)*δ)
    (ht'lo : (9/10)*δ ≤ t') (ht'hi : t' ≤ (11/10)*δ)
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (hratio : M₁ ≤ (11/10)*M₀) :
    ∃ m : ℤ, |(m : ℝ)| *M₁ ≤ 2*M₀ ∧
      ∀ n : ℝ, 0 ≤ n → n ≤ M₁ →
        |(t/M₁-(m : ℝ)*t'/M₀)*n| ≤ (121/200)*δ := by
  have ht' : 0 < t' := by linarith
  obtain ⟨m,hm⟩ := exists_nearest_scaled_integer (t/M₁) (div_pos ht' hM₀)
  have herr : |t/M₁-(m : ℝ)*t'/M₀| ≤ t'/(2*M₀) := by
    simpa only [mul_div_assoc,div_div,mul_comm M₀ (2 : ℝ)] using hm
  have htriangle : |(m : ℝ)*t'/M₀| ≤ |t/M₁|+|t/M₁-(m : ℝ)*t'/M₀| := by
    calc
      |(m : ℝ)*t'/M₀| = |t/M₁ + -(t/M₁-(m : ℝ)*t'/M₀)| := by congr 1; ring
      _ ≤ |t/M₁|+|-(t/M₁-(m : ℝ)*t'/M₀)| := abs_add_le _ _
      _ = |t/M₁|+|t/M₁-(m : ℝ)*t'/M₀| := by rw [abs_neg]
  have hbound : |(m : ℝ)| *t'/M₀ ≤ |t|/M₁+t'/(2*M₀) := by
    have hh := htriangle.trans (add_le_add (le_refl |t/M₁|) herr)
    simpa only [abs_div,abs_mul,abs_of_pos ht',abs_of_pos hM₀,abs_of_pos hM₁] using hh
  have hbound' : |(m : ℝ)| *t'*M₁ ≤ |t| *M₀+t'*M₁/2 := by
    have hh := mul_le_mul_of_nonneg_right hbound (mul_pos hM₀ hM₁).le
    field_simp at hh
    nlinarith
  have hmagnitude : |(m : ℝ)| *M₁ ≤ 2*M₀ := by
    have htM := mul_le_mul_of_nonneg_right ht hM₀.le
    have htr := mul_le_mul_of_nonneg_left hratio ht'.le
    have htloM := mul_le_mul_of_nonneg_right ht'lo hM₀.le
    have hthiM := mul_le_mul_of_nonneg_right ht'hi hM₀.le
    by_contra hh
    have hh' : 2*M₀ < |(m : ℝ)| *M₁ := lt_of_not_ge hh
    have hm' := mul_lt_mul_of_pos_right hh' ht'
    nlinarith
  refine ⟨m,hmagnitude,?_⟩
  intro n hn hnM
  have hscale : t'*M₁ ≤ (121/100)*δ*M₀ := by
    have h1 := mul_le_mul_of_nonneg_right ht'hi hM₁.le
    have h2 := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ (11/10)*δ)
    nlinarith
  calc
    |(t/M₁-(m : ℝ)*t'/M₀)*n| = |t/M₁-(m : ℝ)*t'/M₀| *n := by rw [abs_mul,abs_of_nonneg hn]
    _ ≤ (t'/(2*M₀))*n := mul_le_mul_of_nonneg_right herr hn
    _ ≤ (t'/(2*M₀))*M₁ := mul_le_mul_of_nonneg_left hnM (by positivity)
    _ ≤ (121/200)*δ := by
      have hh : t'*M₁/(2*M₀) ≤ (121/200)*δ := by
        apply (div_le_iff₀ (by positivity : 0 < 2*M₀)).2
        nlinarith
      simpa only [div_mul_eq_mul_div] using hh
end DirectedCycles
