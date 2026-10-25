module

public import DirectedCycles.LocalConvolutionTranslation
public import DirectedCycles.LocalTaylorEstimate

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

omit [Fintype G] in
/-- Local conjugation is used only through its two actual commuting products,
with all composition domains supplied by the stated neighbourhood. -/
theorem derivative_leftShift (hc : L.Cancellative) {R : Set G}
    (hdom : L.AllProductsDefined R 3) {h y c t : G}
    (hh : h ∈ R) (hy : y ∈ R) (hcR : c ∈ R)
    (hhy : L.mulRel h y t) (hyc : L.mulRel y c t)
    (k : G → ℝ) (hk : ∀ x, k x ≠ 0 → x ∈ R) :
    L.derivative h (L.leftShift y k) = L.leftShift y (L.derivative c k) := by
  unfold derivative
  rw [L.leftShift_sub,← L.leftShift_mul hc hdom hh hy hhy k hk,
    ← L.leftShift_mul hc hdom hy hcR hyc k hk]

theorem derivative_convolution_sum (h : G) (f k : G → ℝ) (x : G) :
    L.derivative h (L.convolution f k) x =
      ∑ y : G, f y * L.derivative h (L.leftShift y k) x := by
  change L.leftShift h (fun z => ∑ y : G, f y*L.leftShift y k z) x -
    (∑ y : G, f y*L.leftShift y k x) = _
  rw [L.leftShift_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [L.leftShift_const_mul]
  simp only [derivative,Pi.sub_apply,mul_sub]

/-- The derivative bound depends only on the actual support and actual local
commuting witnesses. There is no assumption of globally defined translations. -/
theorem derivativeNorm_convolution_le (hc : L.Cancellative) {R : Set G}
    (hdom : L.AllProductsDefined R 3) {h : G} (hh : h ∈ R)
    (f k : G → ℝ) (B : Finset G) (hBR : (B : Set G) ⊆ R)
    (hk : ∀ x, k x ≠ 0 → x ∈ R) {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hfs : ∀ y, y ∉ B → f y = 0) (hf : ∀ y ∈ B, |f y| ≤ s)
    (hcomm : ∀ y ∈ B, ∃ c ∈ R, ∃ t, L.mulRel h y t ∧ L.mulRel y c t ∧
      L.derivativeNorm k c ≤ r) :
    L.derivativeNorm (L.convolution f k) h ≤ (B.card : ℝ)*s*r := by
  classical
  apply (L.derivativeNorm_le_iff _ _ (by positivity)).2
  intro x
  rw [L.derivative_convolution_sum]
  have he : (∑ y : G, f y*L.derivative h (L.leftShift y k) x) =
      ∑ y ∈ B, f y*L.derivative h (L.leftShift y k) x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ B)
    intro y _ hy
    rw [hfs y hy,zero_mul]
  rw [he]
  calc
    |∑ y ∈ B, f y*L.derivative h (L.leftShift y k) x| ≤
        ∑ y ∈ B, |f y*L.derivative h (L.leftShift y k) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y ∈ B, s*r := by
      apply Finset.sum_le_sum
      intro y hy
      obtain ⟨c,hcR,t,hhy,hyc,hcBound⟩ := hcomm y hy
      have hshift := L.derivative_leftShift hc hdom hh (hBR hy) hcR hhy hyc k hk
      have hd : |L.derivative h (L.leftShift y k) x| ≤ r := by
        rw [hshift]
        have hp : |L.leftShift y (L.derivative c k) x| ≤ ‖L.leftShift y (L.derivative c k)‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm (L.leftShift y (L.derivative c k)) x
        exact hp.trans ((L.norm_leftShift_le y _).trans hcBound)
      rw [abs_mul]
      exact mul_le_mul (hf y hy) hd (abs_nonneg _) hs
    _ = (B.card : ℝ)*s*r := by simp; ring

/-- The local second derivative estimate required by the Gleason bootstrap. -/
theorem derivativeNorm_twice_convolution_le (hc : L.Cancellative) {R : Set G}
    (hdom : L.AllProductsDefined R 3) {g h : G} (hg : g ∈ R) (hh : h ∈ R)
    (f k : G → ℝ) (B : Finset G) (hBR : (B : Set G) ⊆ R)
    (hf : ∀ x, f x ≠ 0 → x ∈ R) (hk : ∀ x, k x ≠ 0 → x ∈ R)
    {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hfs : ∀ y, y ∉ B → L.derivative g f y = 0)
    (hdf : L.derivativeNorm f g ≤ s)
    (hcomm : ∀ y ∈ B, ∃ c ∈ R, ∃ t, L.mulRel h y t ∧ L.mulRel y c t ∧
      L.derivativeNorm k c ≤ r) :
    L.derivativeNorm (L.derivative g (L.convolution f k)) h ≤ (B.card : ℝ)*s*r := by
  rw [L.derivative_convolution hc hdom hg f k hf hk]
  exact L.derivativeNorm_convolution_le hc hdom hh _ k B hBR hk hs hr hfs
    (fun y _ => (L.abs_derivative_le f g y).trans hdf) hcomm
end LocalGroupAlgebra
end DirectedCycles
