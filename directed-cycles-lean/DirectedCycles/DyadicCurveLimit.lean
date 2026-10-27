module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The rescaled coordinate sequence used to extract the tangent of a
continuous one-parameter map. -/
noncomputable def dyadicCurve (f : ℝ → E) (t : ℝ) (n : ℕ) : E := (2 : ℝ)^n • f (t/(2 : ℝ)^n)

theorem dyadic_argument_bound {r t : ℝ} (ht : |t| ≤ r) (n : ℕ) : |t/(2 : ℝ)^n| ≤ r := by
  rw [abs_div,abs_of_pos (by positivity : (0 : ℝ)<2^n)]
  have hp : (1 : ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
  have hr : 0 ≤ r := (abs_nonneg t).trans ht
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<2^n)).2
  nlinarith

omit [NormedSpace ℝ E] in
/-- A norm expansion factor 3/2 under doubling gives geometric contraction
along every dyadic parameter sequence in the interval. -/
theorem dyadic_curve_norm_bound (f : ℝ → E) {r : ℝ}
    (hc : ∀ t : ℝ, |t| ≤ r → ‖f (t/2)‖ ≤ (2/3)*‖f t‖)
    {t : ℝ} (ht : |t| ≤ r) (n : ℕ) :
    ‖f (t/(2 : ℝ)^n)‖ ≤ (2/3 : ℝ)^n*‖f t‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := hc (t/(2 : ℝ)^n) (dyadic_argument_bound ht n)
    have he : t/(2 : ℝ)^(n+1) = (t/(2 : ℝ)^n)/2 := by rw [pow_succ,div_mul_eq_div_div]
    rw [he,pow_succ]
    nlinarith

/-- Quadratic doubling error and the 3/2 expansion give a summable 8/9
increment bound for the rescaled coordinate sequence. -/
theorem dyadic_curve_increment_bound (f : ℝ → E) {r C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ t : ℝ, |t| ≤ r → ‖f (t/2)‖ ≤ (2/3)*‖f t‖)
    (he : ∀ t : ℝ, |t| ≤ r → ‖f t-(2 : ℝ) • f (t/2)‖ ≤ C*‖f (t/2)‖^2)
    {t : ℝ} (ht : |t| ≤ r) (n : ℕ) :
    dist (dyadicCurve f t n) (dyadicCurve f t (n+1)) ≤
      ((4/9 : ℝ)*C*‖f t‖^2)*(8/9 : ℝ)^n := by
  have harg := dyadic_argument_bound ht n
  have herr := he (t/(2 : ℝ)^n) harg
  have hnorm := dyadic_curve_norm_bound f hc ht (n+1)
  have hdiv : t/(2 : ℝ)^(n+1) = (t/(2 : ℝ)^n)/2 := by rw [pow_succ,div_mul_eq_div_div]
  rw [hdiv] at hnorm
  have hsq : ‖f ((t/(2 : ℝ)^n)/2)‖^2 ≤ ((2/3 : ℝ)^(n+1)*‖f t‖)^2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hdist : dist (dyadicCurve f t n) (dyadicCurve f t (n+1)) =
      (2 : ℝ)^n*‖f (t/(2 : ℝ)^n)-(2 : ℝ) • f ((t/(2 : ℝ)^n)/2)‖ := by
    rw [dist_eq_norm]
    dsimp only [dyadicCurve]
    rw [hdiv,pow_succ,mul_smul,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : (0 : ℝ)<2^n)]
  rw [hdist]
  calc
    (2 : ℝ)^n*‖f (t/(2 : ℝ)^n)-(2 : ℝ) • f ((t/(2 : ℝ)^n)/2)‖ ≤
        2^n*(C*‖f ((t/(2 : ℝ)^n)/2)‖^2) := mul_le_mul_of_nonneg_left herr (by positivity)
    _ ≤ 2^n*(C*((2/3 : ℝ)^(n+1)*‖f t‖)^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hC) (by positivity)
    _ = ((4/9 : ℝ)*C*‖f t‖^2)*(8/9 : ℝ)^n := by
      have hs : ((2/3 : ℝ)^n)^2 = ((2/3 : ℝ)^2)^n := by
        rw [← pow_mul,← pow_mul,Nat.mul_comm]
      have hh : (2 : ℝ)^n * ((2/3 : ℝ)^n)^2 = (8/9 : ℝ)^n := by
        rw [hs,← mul_pow]
        norm_num
      calc
        (2 : ℝ)^n*(C*((2/3 : ℝ)^(n+1)*‖f t‖)^2) =
            ((4/9 : ℝ)*C*‖f t‖^2)*((2 : ℝ)^n*((2/3 : ℝ)^n)^2) := by
              rw [pow_succ (2/3 : ℝ)]
              ring
        _ = _ := by rw [hh]

/-- The dyadic tangent limit exists in every complete real normed space, and
its distance from the original coordinate is quadratically controlled. -/
theorem exists_dyadic_curve_limit [CompleteSpace E] (f : ℝ → E) {r C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ t : ℝ, |t| ≤ r → ‖f (t/2)‖ ≤ (2/3)*‖f t‖)
    (he : ∀ t : ℝ, |t| ≤ r → ‖f t-(2 : ℝ) • f (t/2)‖ ≤ C*‖f (t/2)‖^2)
    {t : ℝ} (ht : |t| ≤ r) :
    ∃ v : E, Filter.Tendsto (dyadicCurve f t) Filter.atTop (𝓝 v) ∧ ‖v-f t‖ ≤ 4*C*‖f t‖^2 := by
  have hb := dyadic_curve_increment_bound f hC hc he ht
  have hca := cauchySeq_of_le_geometric (8/9 : ℝ) ((4/9 : ℝ)*C*‖f t‖^2) (by norm_num) hb
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hca
  refine ⟨v,hv,?_⟩
  have hh := dist_le_of_le_geometric_of_tendsto₀ (8/9 : ℝ) ((4/9 : ℝ)*C*‖f t‖^2) (by norm_num) hb hv
  simp only [dyadicCurve,pow_zero,div_one,one_smul] at hh
  rw [dist_eq_norm,norm_sub_rev] at hh
  convert hh using 1
  ring
end DirectedCycles
