module

public import DirectedCycles.LocalConvolutionTranslation
public import DirectedCycles.LocalTaylorEstimate

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

/-- For fixed output, the local convolution kernel counts each right factor
at most once. This is the correct replacement for global change of variables. -/
theorem sum_leftShift_le (hc : L.Cancellative) (k : G → ℝ) (hk : ∀ x, 0 ≤ k x) (x : G) :
    (∑ y : G, L.leftShift y k x) ≤ ∑ z : G, k z := by
  classical
  simp only [L.leftShift_eq_sum hc]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro z _
  by_cases h : ∃ y, L.mulRel y z x
  · obtain ⟨y,hy⟩ := h
    rw [Finset.sum_eq_single y]
    · rw [ite_eq_left hy]
    · intro a _ hay
      exact ite_eq_right (fun ha => hay (hc.right_cancel ha hy))
    · simp
  · have he : (∑ y : G, if L.mulRel y z x then k z else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      exact ite_eq_right (fun hy => h ⟨y,hy⟩)
    rw [he]
    exact hk z

/-- Convolution is bounded by a uniform first-factor bound times the mass of
the nonnegative second factor, using local cancellation only. -/
theorem norm_convolution_le (hc : L.Cancellative) (f k : G → ℝ)
    (hk : ∀ x, 0 ≤ k x) {s : ℝ} (hs : 0 ≤ s) (hf : ∀ x, |f x| ≤ s) :
    ‖L.convolution f k‖ ≤ s*∑ z : G, k z := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hs (Finset.sum_nonneg fun z _ => hk z))).2
  intro x
  rw [Real.norm_eq_abs]
  change |∑ y : G, f y*L.leftShift y k x| ≤ _
  calc
    |∑ y : G, f y*L.leftShift y k x| ≤ ∑ y : G, |f y*L.leftShift y k x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y : G, s*L.leftShift y k x := by
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul,abs_of_nonneg (L.leftShift_nonneg hk y x)]
      exact mul_le_mul_of_nonneg_right (hf y) (L.leftShift_nonneg hk y x)
    _ = s*∑ y : G, L.leftShift y k x := (Finset.mul_sum _ _ _).symm
    _ ≤ s*∑ z : G, k z := mul_le_mul_of_nonneg_left (L.sum_leftShift_le hc k hk x) hs

theorem derivativeNorm_convolution_mass_le (hc : L.Cancellative) {R : Set G}
    (hdom : L.AllProductsDefined R 3) {g : G} (hg : g ∈ R)
    (f k : G → ℝ) (hf : ∀ x, f x ≠ 0 → x ∈ R) (hkR : ∀ x, k x ≠ 0 → x ∈ R)
    (hk : ∀ x, 0 ≤ k x) :
    L.derivativeNorm (L.convolution f k) g ≤ L.derivativeNorm f g * ∑ z : G, k z := by
  unfold derivativeNorm
  rw [L.derivative_convolution hc hdom hg f k hf hkR]
  exact L.norm_convolution_le hc _ k hk (L.derivativeNorm_nonneg f g) (L.abs_derivative_le f g)
end LocalGroupAlgebra
end DirectedCycles
