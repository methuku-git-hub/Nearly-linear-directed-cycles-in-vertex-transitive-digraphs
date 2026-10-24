import DirectedCycles.LieExponentialProductCoordinates
import DirectedCycles.LieExponentialSymmetry

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ,E) ∞ G]

/-- The actual group difference of nearby exponential values has the
additive difference coordinate plus an arbitrarily small first-order error. -/
theorem lie_exponential_difference_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ x y : E, ‖x‖ < R → ‖y‖ < R →
      ∃ z : E, ‖z‖ ≤ ‖y-x‖+ε*(‖x‖+‖y‖) ∧
        lieExponential (G := G) z = (lieExponential x)⁻¹*lieExponential y := by
  obtain ⟨ν,hν0,hν,heq⟩ := lie_exponential_product_coordinates (G := G) (E := E)
  have he := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hν).bound hε
  have he' : ∀ᶠ p : E × E in 𝓝 (0,0), ‖ν p-(p.1+p.2)‖ ≤ ε*‖p‖ := by
    filter_upwards [he] with p hp
    change ‖ν ((0 : E × E)+p)-ν (0,0)-(p.1+p.2)‖ ≤ ε*‖p‖ at hp
    simpa only [zero_add,hν0,sub_zero] using hp
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (he'.and heq)
  refine ⟨R,hR,?_⟩
  intro x y hx hy
  have hp : (-x,y) ∈ Metric.ball (0,0) R := by
    simp only [Metric.mem_ball,Prod.dist_eq,dist_zero_right,norm_neg]
    exact max_lt hx hy
  obtain ⟨hb,he⟩ := hball hp
  have hb' : ‖ν (-x,y)-(y-x)‖ ≤ ε*‖(-x,y)‖ := by simpa only [sub_eq_add_neg,add_comm] using hb
  have hpn : ‖(-x,y)‖ ≤ ‖x‖+‖y‖ := by
    simp only [Prod.norm_def,norm_neg]
    exact max_le (le_add_of_nonneg_right (norm_nonneg y)) (le_add_of_nonneg_left (norm_nonneg x))
  refine ⟨ν (-x,y),?_,?_⟩
  · have ht := norm_le_insert' (ν (-x,y)) (y-x)
    have hm := mul_le_mul_of_nonneg_left hpn hε.le
    linarith
  · simpa only [lieExponential_neg] using he
end DirectedCycles
