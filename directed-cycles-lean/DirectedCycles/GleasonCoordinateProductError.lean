import DirectedCycles.GleasonCoordinateSpeed

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : GleasonLieAlgebra D ≃L[ℝ] E)

theorem coordinateExp_neg (x : E) : coordinateExp D e (-x) = (coordinateExp D e x)⁻¹ := by
  rw [show -x = (-1 : ℝ) • x by simp,coordinateExp_smul]
  change (toOneParameter D (e.symm x)).eval (-1) = ((toOneParameter D (e.symm x)).eval 1)⁻¹
  exact OneParameter.eval_neg _ _

/-- The quantitative Trotter error in fixed linear coordinates. -/
theorem coordinateExp_add_error {r A : ℝ}
    (hp : ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r →
      (n : ℝ)*D.gauge h ≤ r → D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h)
    (hr : r ≤ 1/(8*D.constant)) (hA : 0 ≤ A)
    (hspeed : ∀ x : E, ∀ t : ℝ, D.gauge ((toOneParameter D (e.symm x)).eval t) ≤ A*‖x‖*|t|)
    (x y : E) (hsmall : A*(‖x‖+‖y‖) ≤ r) :
    D.metric.dist (coordinateExp D e x*coordinateExp D e y) (coordinateExp D e (x+y)) ≤
      4*D.constant*A^2*‖x‖*‖y‖ := by
  have h := exp_add_error D hp hr (e.symm x) (e.symm y)
    (mul_nonneg hA (norm_nonneg x)) (mul_nonneg hA (norm_nonneg y))
    (hspeed x) (hspeed y) (by simpa only [mul_add] using hsmall)
  change D.metric.dist (exp D (e.symm x)*exp D (e.symm y)) (exp D (e.symm (x+y))) ≤ _
  rw [map_add]
  exact h.trans_eq (by ring)

/-- Gauge comparison of a coordinate difference and the actual group
distance; the discrepancy is quadratic in the two input norms. -/
theorem coordinate_difference_gauge_error {r A : ℝ}
    (hp : ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r →
      (n : ℝ)*D.gauge h ≤ r → D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h)
    (hr : r ≤ 1/(8*D.constant)) (hA : 0 ≤ A)
    (hspeed : ∀ x : E, ∀ t : ℝ, D.gauge ((toOneParameter D (e.symm x)).eval t) ≤ A*‖x‖*|t|)
    (x y : E) (hsmall : A*(‖x‖+‖y‖) ≤ r) :
    D.gauge (coordinateExp D e (y-x)) ≤ D.metric.dist (coordinateExp D e x) (coordinateExp D e y)+4*D.constant*A^2*‖x‖*‖y‖ ∧
    D.metric.dist (coordinateExp D e x) (coordinateExp D e y) ≤ D.gauge (coordinateExp D e (y-x))+4*D.constant*A^2*‖x‖*‖y‖ := by
  have h := coordinateExp_add_error D e hp hr hA hspeed (-x) y (by simpa only [norm_neg] using hsmall)
  rw [coordinateExp_neg,norm_neg,show -x+y=y-x by abel] at h
  let p := (coordinateExp D e x)⁻¹*coordinateExp D e y
  let z := coordinateExp D e (y-x)
  have h₁ := D.metric.dist_triangle 1 p z
  have h₂ := D.metric.dist_triangle 1 z p
  rw [D.metric.dist_comm z p] at h₂
  change D.gauge z ≤ D.gauge p+D.metric.dist p z at h₁
  change D.gauge p ≤ D.gauge z+D.metric.dist p z at h₂
  rw [D.dist_eq_gauge]
  exact ⟨h₁.trans (add_le_add_right h _),h₂.trans (add_le_add_right h _)⟩

end DirectedCycles.GleasonLieAlgebra
