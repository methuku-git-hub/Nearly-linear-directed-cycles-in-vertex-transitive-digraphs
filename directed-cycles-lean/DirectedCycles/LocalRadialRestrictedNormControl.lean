import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace DirectedCycles
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Local injectivity controls the tangent using only radial parameters
inside the actual injectivity ball. No global exponential curve is required. -/
theorem radial_norm_le_of_locally_bounded_image (exp : E → G) {R ρ a : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ < R) (ha : 0 < a)
    (hinj : Set.InjOn exp (Metric.ball 0 R)) (v : E)
    (himage : ∀ t : ℝ, |t| ≤ a → |t| * ‖v‖ < R → exp (t • v) ∈ exp '' Metric.closedBall 0 ρ) :
    a*‖v‖ ≤ ρ := by
  by_contra hn
  have hnv : 0 < ‖v‖ := by
    have hgt : ρ < a*‖v‖ := lt_of_not_ge hn
    by_contra hh
    have hz : ‖v‖ = 0 := le_antisymm (le_of_not_gt hh) (norm_nonneg v)
    rw [hz,mul_zero] at hgt
    linarith
  let b := (ρ+R)/2
  have hρb : ρ < b := by dsimp only [b]; linarith
  have hbR : b < R := by dsimp only [b]; linarith
  have hb : 0 < b := lt_of_le_of_lt hρ hρb
  let t := min a (b/‖v‖)
  have ht : 0 < t := lt_min ha (div_pos hb hnv)
  have hta : t ≤ a := min_le_left _ _
  have htn : t*‖v‖ = min (a*‖v‖) b := by
    dsimp only [t]
    rw [min_mul_of_nonneg _ _ (norm_nonneg v),div_mul_cancel₀ _ hnv.ne']
  have hgt : ρ < t*‖v‖ := by rw [htn]; exact lt_min (lt_of_not_ge hn) hρb
  have hlt : t*‖v‖ < R := by rw [htn]; exact (min_le_right _ _).trans_lt hbR
  have htv : t • v ∈ Metric.ball 0 R := by
    simpa only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos ht] using hlt
  obtain ⟨w,hw,he⟩ := himage t (by rw [abs_of_pos ht]; exact hta) (by rw [abs_of_pos ht]; exact hlt)
  have hwn : ‖w‖ ≤ ρ := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
  have hwR : w ∈ Metric.ball 0 R := by simpa only [Metric.mem_ball,dist_zero_right] using hwn.trans_lt hρR
  have hwe : w = t • v := hinj hwR htv he
  rw [hwe,norm_smul,Real.norm_eq_abs,abs_of_pos ht] at hwn
  exact (not_lt_of_ge hwn) hgt
end DirectedCycles
