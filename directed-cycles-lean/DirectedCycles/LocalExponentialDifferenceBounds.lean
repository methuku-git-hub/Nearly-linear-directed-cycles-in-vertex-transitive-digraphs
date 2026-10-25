module

public import DirectedCycles.LocalExponentialProductBounds
public import DirectedCycles.LocalExponentialRadialLaw

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
namespace LocalExponentialData
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] {L : LocalGroupAlgebra G} (D : LocalExponentialData (E := E) L)

/-- Local relative differences have a coordinate as close to subtraction as
prescribed. The exact inverse and product relation accompany the estimate. -/
theorem difference_norm_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ x y : E, ‖x‖ < R → ‖y‖ < R →
      ∃ z : E, ‖z‖ ≤ ‖y-x‖+ε*(‖x‖+‖y‖) ∧
        L.mulRel (L.inv (D.chart x)) (D.chart y) (D.chart z) := by
  obtain ⟨a,ha,hadd⟩ := D.product_add_error hε
  refine ⟨min a (D.radius/4),lt_min ha (by have := D.radius_pos; positivity),?_⟩
  intro x y hx hy
  obtain ⟨z,hz,hrel⟩ := hadd (-x) y (by simpa only [norm_neg] using hx.trans_le (min_le_left _ _))
    (hy.trans_le (min_le_left _ _))
  have hinv : D.chart (-x) = L.inv (D.chart x) := D.inv_chart (by
    have := hx.trans_le (min_le_right _ _)
    have := D.radius_pos
    linarith)
  rw [hinv] at hrel
  have herr : ‖z-(y-x)‖ ≤ ε*(‖x‖+‖y‖) := by
    simpa only [norm_neg,sub_eq_add_neg,add_comm] using hz
  exact ⟨z,(norm_le_insert' z (y-x)).trans (add_le_add_right herr _),hrel⟩
end LocalExponentialData
end DirectedCycles
