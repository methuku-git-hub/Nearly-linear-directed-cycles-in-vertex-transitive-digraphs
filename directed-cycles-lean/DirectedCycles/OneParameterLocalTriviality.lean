import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- An additive-parameter group homomorphism trivial on a neighbourhood of zero
is trivial everywhere, by an actual finite subdivision of each parameter. -/
theorem one_parameter_trivial_of_eventually_one (φ : ℝ → G) (h0 : φ 0 = 1)
    (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t)
    (hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), φ t = 1) : ∀ t : ℝ, φ t = 1 := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hnat : ∀ n : ℕ, ∀ s : ℝ, φ ((n : ℝ)*s) = (φ s)^n := by
    intro n s
    induction n with
    | zero => simpa only [Nat.cast_zero,zero_mul,pow_zero] using h0
    | succ n ih =>
      rw [Nat.cast_succ,add_mul,one_mul,hadd,ih,pow_succ]
  intro t
  obtain ⟨n,hn⟩ := exists_nat_gt (|t|/r+1)
  have hnpos : 0 < (n : ℝ) := by have := div_nonneg (abs_nonneg t) hr.le; linarith
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have ht : |t/(n : ℝ)| < r := by
    rw [abs_div,abs_of_pos hnpos]
    apply (div_lt_iff₀ hnpos).2
    have hh := (div_lt_iff₀ hr).1 (show |t|/r < (n : ℝ) by linarith)
    nlinarith
  have hone : φ (t/(n : ℝ)) = 1 :=
    hball (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)
  have hh := hnat n (t/(n : ℝ))
  rw [mul_div_cancel₀ _ hn0,hone,one_pow] at hh
  exact hh
end DirectedCycles
