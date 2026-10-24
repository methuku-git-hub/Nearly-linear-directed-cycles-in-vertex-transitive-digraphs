import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A map with addition derivative has an arbitrarily close to additive
norm bound on an actual product neighbourhood. -/
theorem addition_derivative_norm_bound (f : E × E → E) (h0 : f (0,0) = 0)
    (hf : HasFDerivAt f (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (0,0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ x y : E, ‖x‖ < r → ‖y‖ < r →
      ‖f (x,y)‖ ≤ (1+ε)*(‖x‖+‖y‖) := by
  have he := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hf).bound hε
  have he' : ∀ᶠ p : E × E in 𝓝 0, ‖f p-(p.1+p.2)‖ ≤ ε*‖p‖ := by
    filter_upwards [he] with p hp
    change ‖f ((0 : E × E)+p)-f (0,0)-(p.1+p.2)‖ ≤ ε*‖p‖ at hp
    simpa only [zero_add,h0,sub_zero] using hp
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp he'
  refine ⟨r,hr,?_⟩
  intro x y hx hy
  have hp : (x,y) ∈ Metric.ball 0 r := by
    simp only [Metric.mem_ball,dist_zero_right,Prod.norm_def]
    exact max_lt hx hy
  have herr : ‖f (x,y)-(x+y)‖ ≤ ε*‖(x,y)‖ := hball hp
  have hprod : ‖(x,y)‖ ≤ ‖x‖+‖y‖ := by
    rw [Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg y)) (le_add_of_nonneg_left (norm_nonneg x))
  have htri : ‖f (x,y)‖ ≤ ‖f (x,y)-(x+y)‖+‖x+y‖ := by simpa only [add_comm] using norm_le_insert' (f (x,y)) (x+y)
  have hsum := norm_add_le x y
  have hmul := mul_le_mul_of_nonneg_left hprod hε.le
  nlinarith
end DirectedCycles
