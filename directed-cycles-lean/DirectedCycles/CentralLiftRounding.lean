module

public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Round the actual scaled coefficient. Rounding a surrogate coefficient and
then dropping the sign of its error is unnecessary. -/
theorem exists_nearest_scaled_integer (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ m : ℤ, |a-(m : ℝ)*b| ≤ b/2 := by
  refine ⟨round (a/b),?_⟩
  have h := mul_le_mul_of_nonneg_right (abs_sub_round (a/b)) hb.le
  have he : |a/b-(round (a/b) : ℝ)| * b = |a-(round (a/b) : ℝ)*b| := by
    calc
      |a/b-(round (a/b) : ℝ)| * b = |a/b-(round (a/b) : ℝ)| * |b| := by rw [abs_of_pos hb]
      _ = |(a/b-(round (a/b) : ℝ))*b| := (abs_mul _ _).symm
      _ = |a-(round (a/b) : ℝ)*b| := by rw [sub_mul,div_mul_cancel₀ a hb.ne']
  rw [he] at h
  linarith

/-- The quantitative rounding step for central lift improvement, with room
for the 1.1 distortions in both the coordinate and the escape-time ratio. -/
theorem central_lift_rounding {δ t t' M₀ M₁ : ℝ} (hδ : 0 < δ)
    (ht' : 0 < t') (ht'upper : t' ≤ (11/10)*δ)
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (hratio : M₁ ≤ (11/10)*M₀) :
    ∃ m : ℤ, ∀ n : ℝ, 0 ≤ n → n ≤ M₁ →
      |(t/M₁-(m : ℝ)*t'/M₀)*n| ≤ (121/200)*δ := by
  obtain ⟨m,hm⟩ := exists_nearest_scaled_integer (t/M₁) (div_pos ht' hM₀)
  refine ⟨m,?_⟩
  intro n hn hnM
  have he : |t/M₁-(m : ℝ)*t'/M₀| ≤ t'/(2*M₀) := by
    simpa only [mul_div_assoc,div_div,mul_comm M₀ (2 : ℝ)] using hm
  have hscale : t'*M₁ ≤ (121/100)*δ*M₀ := by
    have h1 := mul_le_mul_of_nonneg_right ht'upper hM₁.le
    have h2 := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ (11/10)*δ)
    nlinarith
  calc
    |(t/M₁-(m : ℝ)*t'/M₀)*n| = |t/M₁-(m : ℝ)*t'/M₀| *n := by rw [abs_mul,abs_of_nonneg hn]
    _ ≤ (t'/(2*M₀))*n := mul_le_mul_of_nonneg_right he hn
    _ ≤ (t'/(2*M₀))*M₁ := mul_le_mul_of_nonneg_left hnM (by positivity)
    _ ≤ (121/200)*δ := by
      have h : t'*M₁/(2*M₀) ≤ (121/200)*δ := by
        apply (div_le_iff₀ (by positivity : 0 < 2*M₀)).2
        nlinarith
      simpa only [div_mul_eq_mul_div] using h
end DirectedCycles
