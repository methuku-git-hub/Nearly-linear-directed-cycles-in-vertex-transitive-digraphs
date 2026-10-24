import DirectedCycles.LocalMultiplicativeCurveUniqueness

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*}

/-- Two local multiplicative curves that agree near zero agree throughout
the common multiplication interval. Finite subdivision uses only the given
local law; it never extends a local ambient group to a global one. -/
theorem local_multiplicative_eq_of_eventually_eq (μ : E × E → E) (f g : ℝ → E)
    (h0 : f 0 = g 0) {r s : ℝ}
    (hf : ∀ a b : ℝ, |a|+|b| ≤ r → f (a+b) = μ (f a,f b))
    (hg : ∀ a b : ℝ, |a|+|b| ≤ s → g (a+b) = μ (g a,g b))
    (hnear : f =ᶠ[𝓝 (0 : ℝ)] g) (t : ℝ) (htr : |t| ≤ r) (hts : |t| ≤ s) : f t = g t := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨n,hn⟩ := exists_nat_gt (|t|/δ+1)
  have hnpos : 0 < (n : ℝ) := by have := div_nonneg (abs_nonneg t) hδ.le; linarith
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  let u : ℝ := t/n
  have hu : |u| < δ := by
    dsimp only [u]
    rw [abs_div,abs_of_pos hnpos]
    apply (div_lt_iff₀ hnpos).2
    have hh := (div_lt_iff₀ hδ).1 (show |t|/δ < (n : ℝ) by linarith)
    nlinarith
  have he : f u = g u := hball (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hu)
  have hstep : ∀ k : ℕ, k+1 ≤ n → |(k : ℝ)*u|+|u| ≤ |t| := by
    intro k hk
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg k)]
    have hkn : (k : ℝ)+1 ≤ n := by exact_mod_cast hk
    have huabs : |u| = |t|/(n : ℝ) := by dsimp only [u]; rw [abs_div,abs_of_pos hnpos]
    rw [huabs]
    have h := mul_le_mul_of_nonneg_right hkn (div_nonneg (abs_nonneg t) hnpos.le)
    rw [mul_div_cancel₀ _ hn0] at h
    nlinarith
  have hall : ∀ k : ℕ, k ≤ n → f ((k : ℝ)*u) = g ((k : ℝ)*u) := by
    intro k
    induction k with
    | zero => intro _; simpa only [Nat.cast_zero,zero_mul] using h0
    | succ k ih =>
      intro hk
      rw [Nat.cast_succ,add_mul,one_mul,hf _ _ ((hstep k hk).trans htr),
        hg _ _ ((hstep k hk).trans hts),ih (by omega),he]
  simpa only [u,mul_div_cancel₀ _ hn0] using hall n le_rfl

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The tangent determines a smooth local multiplicative curve on its entire
given interval, by ODE germ uniqueness followed by actual subdivision. -/
theorem local_multiplicative_curve_unique (μ : E × E → E)
    (hμ : ContDiffAt ℝ 2 μ (0,0)) (f g : ℝ → E) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    {v : E} (hfv : HasDerivAt f v 0) (hgv : HasDerivAt g v 0)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hfadd : ∀ a b : ℝ, |a|+|b| ≤ r → f (a+b) = μ (f a,f b))
    (hgadd : ∀ a b : ℝ, |a|+|b| ≤ s → g (a+b) = μ (g a,g b))
    (t : ℝ) (htr : |t| ≤ r) (hts : |t| ≤ s) : f t = g t :=
  local_multiplicative_eq_of_eventually_eq μ f g (hf0.trans hg0.symm) hfadd hgadd
    (local_multiplicative_curve_eventually_unique μ hμ f g hf0 hg0 hfv hgv hr hs hfadd hgadd) t htr hts
end DirectedCycles
