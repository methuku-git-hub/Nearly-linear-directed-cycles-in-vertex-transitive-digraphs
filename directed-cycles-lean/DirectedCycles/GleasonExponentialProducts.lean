module

public import DirectedCycles.GleasonApproximateProduct
public import DirectedCycles.GleasonCoordinateProductError

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- Uniform quadratic control of arbitrary finite ordered exponential
products by the exponential of their vector sum. -/
theorem exists_coordinateExp_ordered_product_bound : ∃ K ρ : ℝ, 0 < K ∧ 0 < ρ ∧
    ∀ (v : ℕ → E) (n : ℕ), (∑ j ∈ Finset.range n, ‖v j‖) ≤ ρ →
      D.metric.dist (((List.range n).map (fun j => coordinateExp D e (v j))).prod)
        (coordinateExp D e (∑ j ∈ Finset.range n, v j)) ≤
        K*(∑ j ∈ Finset.range n, ‖v j‖)^2 := by
  obtain ⟨A,hA,hspeed⟩ := exists_coordinate_speed D e
  obtain ⟨r,hr,hrC,hp⟩ := D.exists_trotter_radius
  let K := 4*D.constant*A^2
  let ρ := min ((r/A)/2) (min (1/(2*A*D.constant)) (min 1 (1/(K*D.constant))))
  have hC := D.constant_pos
  have hK : 0 < K := by dsimp [K]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  refine ⟨2*K,ρ,by positivity,hρ,?_⟩
  intro v n hv
  let S := ∑ j ∈ Finset.range n, ‖v j‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => norm_nonneg (v j))
  have hSr : S ≤ (r/A)/2 := hv.trans (min_le_left _ _)
  have hSw : S ≤ 1/(2*A*D.constant) := hv.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hS1 : S ≤ 1 := hv.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hSK : S ≤ 1/(K*D.constant) := hv.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hwindow : 2*A*S ≤ 1/D.constant := by
    apply (le_div_iff₀ hC).mpr
    have hh := (le_div_iff₀ (show 0 < 2*A*D.constant by positivity)).mp hSw
    nlinarith
  have hquad : K*S^2 ≤ 1/D.constant := by
    have hh := (le_div_iff₀ (mul_pos hK hC)).mp hSK
    have hks : K*S ≤ 1/D.constant := (le_div_iff₀ hC).mpr (by nlinarith)
    exact (mul_le_mul_of_nonneg_left (show S^2 ≤ S by nlinarith) hK.le).trans hks
  have herr (x y : E) (hxy : ‖x‖+‖y‖ ≤ r/A) :
      D.metric.dist (coordinateExp D e x*coordinateExp D e y) (coordinateExp D e (x+y)) ≤ K*‖x‖*‖y‖ := by
    apply coordinateExp_add_error D e hp hrC hA.le hspeed
    have h := (le_div_iff₀ hA).mp hxy
    nlinarith
  have h := D.approximate_product (coordinateExp D e) (coordinateExp_zero D e) hA.le hK.le
    (coordinateExp_gauge_bound D e hspeed) herr v n (by change 2*S ≤ r/A; linarith) hwindow hquad
  exact h.trans_eq (by ring)

end DirectedCycles.GleasonLieAlgebra
