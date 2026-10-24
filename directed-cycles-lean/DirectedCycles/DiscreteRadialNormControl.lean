import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace DirectedCycles
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Consecutive integer points in a small radial image cannot jump between
exponential preimages: the next point stays in the injective ball. -/
theorem discrete_radial_norm_le (exp : E → G) {R ρ : ℝ} (hρ : 0 ≤ ρ)
    (hR : 2*ρ < R) (hinj : Set.InjOn exp (Metric.ball 0 R))
    (v : E) (hv : ‖v‖ ≤ ρ) (N : ℕ)
    (hp : ∀ n ≤ N, exp ((n : ℝ) • v) ∈ exp '' Metric.closedBall 0 ρ) :
    (N : ℝ)*‖v‖ ≤ ρ := by
  have hall : ∀ n ≤ N, (n : ℝ)*‖v‖ ≤ ρ := by
    intro n
    induction n with
    | zero => intro _; simpa using hρ
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hsmall : ‖((n+1 : ℕ) : ℝ) • v‖ < R := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
        push_cast
        nlinarith
      obtain ⟨w,hw,he⟩ := hp (n+1) hn
      have hwn : ‖w‖ ≤ ρ := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
      have hwR : w ∈ Metric.ball 0 R := by
        simp only [Metric.mem_ball,dist_zero_right]
        linarith
      have hnv : ((n+1 : ℕ) : ℝ) • v ∈ Metric.ball 0 R := by
        simpa only [Metric.mem_ball,dist_zero_right] using hsmall
      have hwv := hinj hwR hnv he
      rw [hwv,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)] at hwn
      exact hwn
  exact hall N le_rfl
end DirectedCycles
