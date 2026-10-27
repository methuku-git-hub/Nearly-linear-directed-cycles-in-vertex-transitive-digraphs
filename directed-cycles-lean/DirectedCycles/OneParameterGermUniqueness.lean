module

public import DirectedCycles.OneParameterLocalTriviality

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- Agreement near zero determines an additive-parameter group homomorphism
globally, by finite subdivision. No commutativity between two curves is assumed. -/
theorem one_parameter_eq_of_eventually_eq (φ ψ : ℝ → G) (h0 : φ 0 = 1) (hψ0 : ψ 0 = 1)
    (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (hψadd : ∀ s t : ℝ, ψ (s+t) = ψ s*ψ t)
    (hnear : φ =ᶠ[𝓝 (0 : ℝ)] ψ) : φ = ψ := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hnat : ∀ n : ℕ, ∀ s : ℝ, φ ((n : ℝ)*s) = (φ s)^n := by
    intro n s
    induction n with
    | zero => simpa only [Nat.cast_zero,zero_mul,pow_zero] using h0
    | succ n ih =>
      rw [Nat.cast_succ,add_mul,one_mul,hadd,ih,pow_succ]
  have hnatψ : ∀ n : ℕ, ∀ s : ℝ, ψ ((n : ℝ)*s) = (ψ s)^n := by
    intro n s
    induction n with
    | zero => simpa only [Nat.cast_zero,zero_mul,pow_zero] using hψ0
    | succ n ih =>
      rw [Nat.cast_succ,add_mul,one_mul,hψadd,ih,pow_succ]
  funext t
  obtain ⟨n,hn⟩ := exists_nat_gt (|t|/r+1)
  have hnpos : 0 < (n : ℝ) := by have := div_nonneg (abs_nonneg t) hr.le; linarith
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have ht : |t/(n : ℝ)| < r := by
    rw [abs_div,abs_of_pos hnpos]
    apply (div_lt_iff₀ hnpos).2
    have hh := (div_lt_iff₀ hr).1 (show |t|/r < (n : ℝ) by linarith)
    nlinarith
  have hone : φ (t/(n : ℝ)) = ψ (t/(n : ℝ)) :=
    hball (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)
  have hh := hnat n (t/(n : ℝ))
  rw [mul_div_cancel₀ _ hn0,hone] at hh
  have hhψ := hnatψ n (t/(n : ℝ))
  rw [mul_div_cancel₀ _ hn0] at hhψ
  exact hh.trans hhψ.symm
end DirectedCycles
