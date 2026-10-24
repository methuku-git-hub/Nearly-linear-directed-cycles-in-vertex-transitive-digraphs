import DirectedCycles.SmoothLocalExponentialChart
import DirectedCycles.AdditionDerivativeNormBound

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
namespace LocalExponentialData
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] {L : LocalGroupAlgebra G} (D : LocalExponentialData (E := E) L)

/-- Actual local products have exponential coordinates satisfying an
arbitrarily sharp sum bound. The multiplication relation is part of the
conclusion, so no undefined product is evaluated. -/
theorem product_norm_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ x y : E, ‖x‖ < r → ‖y‖ < r →
      ∃ z : E, ‖z‖ ≤ (1+ε)*(‖x‖+‖y‖) ∧ L.mulRel (D.chart x) (D.chart y) (D.chart z) := by
  obtain ⟨a,ha,habound⟩ := addition_derivative_norm_bound D.product D.product_zero D.product_derivative hε
  obtain ⟨b,hb,hbeq⟩ := Metric.mem_nhds_iff.mp D.product_rel
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro x y hx hy
  refine ⟨D.product (x,y),habound x y (hx.trans_le (min_le_left _ _))
    (hy.trans_le (min_le_left _ _)),?_⟩
  exact hbeq (show (x,y) ∈ Metric.ball (0,0) b from by
    simpa only [Metric.mem_ball,Prod.dist_eq,dist_zero_right] using
      max_lt (hx.trans_le (min_le_right _ _)) (hy.trans_le (min_le_right _ _)))

/-- The actual local product differs from coordinate addition by a prescribed
first-order error throughout a constructed neighbourhood. -/
theorem product_add_error {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ x y : E, ‖x‖ < r → ‖y‖ < r →
      ∃ z : E, ‖z-(x+y)‖ ≤ ε*(‖x‖+‖y‖) ∧ L.mulRel (D.chart x) (D.chart y) (D.chart z) := by
  have he := (hasFDerivAt_iff_isLittleO_nhds_zero.mp D.product_derivative).bound hε
  have he' : ∀ᶠ p : E × E in 𝓝 (0,0), ‖D.product p-(p.1+p.2)‖ ≤ ε*‖p‖ := by
    filter_upwards [he] with p hp
    change ‖D.product ((0 : E × E)+p)-D.product (0,0)-(p.1+p.2)‖ ≤ ε*‖p‖ at hp
    simpa only [zero_add,D.product_zero,sub_zero] using hp
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (he'.and D.product_rel)
  refine ⟨r,hr,?_⟩
  intro x y hx hy
  obtain ⟨hb,hrel⟩ := hball (show (x,y) ∈ Metric.ball (0,0) r from by
    simpa only [Metric.mem_ball,Prod.dist_eq,dist_zero_right] using max_lt hx hy)
  have hp : ‖(x,y)‖ ≤ ‖x‖+‖y‖ := by
    rw [Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg y)) (le_add_of_nonneg_left (norm_nonneg x))
  exact ⟨D.product (x,y),hb.trans (mul_le_mul_of_nonneg_left hp hε.le),hrel⟩
end LocalExponentialData
end DirectedCycles
