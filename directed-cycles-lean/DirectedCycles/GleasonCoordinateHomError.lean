import DirectedCycles.GleasonCoordinateProductError
import DirectedCycles.GleasonNormedHomLipschitz

set_option autoImplicit false
namespace DirectedCycles.GleasonLieAlgebra
variable {G E A : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : GleasonLieAlgebra D ≃L[ℝ] E)
    [NormedRing A] [NormedAlgebra ℝ A]

/-- Continuous algebra-valued homomorphisms preserve the quadratic
coordinate product estimate, with constructed uniform constants. -/
theorem coordinateHom_add_error (F : ContinuousMonoidHom G A) : ∃ K δ : ℝ,
    0 < K ∧ 0 < δ ∧ ∀ x y : E, ‖x‖ < δ → ‖y‖ < δ →
      ‖F (coordinateExp D e x)*F (coordinateExp D e y)-F (coordinateExp D e (x+y))‖ ≤ K*‖x‖*‖y‖ := by
  obtain ⟨L,u,hL,hu,hLip⟩ := D.continuous_hom_locally_lipschitz F
  obtain ⟨B,hB,hspeed⟩ := exists_coordinate_speed D e
  obtain ⟨r,hrpos,hr,hp⟩ := D.exists_trotter_radius
  have hC := D.constant_pos
  let δ := min (r/(4*B)) (u/(4*B))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨L*(4*D.constant*B^2),δ,by positivity,hδ,?_⟩
  intro x y hx hy
  have hrδ := (le_div_iff₀ (show 0 < 4*B by positivity)).mp (min_le_left (r/(4*B)) (u/(4*B)))
  have huδ := (le_div_iff₀ (show 0 < 4*B by positivity)).mp (min_le_right (r/(4*B)) (u/(4*B)))
  have hsmall : B*(‖x‖+‖y‖) ≤ r := by nlinarith
  have hsmallu : B*(‖x‖+‖y‖) ≤ u := by nlinarith
  have hprod : D.gauge (coordinateExp D e x*coordinateExp D e y) ≤ u :=
    (D.gauge_mul_le _ _).trans ((add_le_add (coordinateExp_gauge_bound D e hspeed x)
      (coordinateExp_gauge_bound D e hspeed y)).trans (by nlinarith))
  have hsum : D.gauge (coordinateExp D e (x+y)) ≤ u :=
    (coordinateExp_gauge_bound D e hspeed (x+y)).trans
      ((mul_le_mul_of_nonneg_left (norm_add_le x y) hB.le).trans hsmallu)
  have h := (hLip _ _ hprod hsum).trans (mul_le_mul_of_nonneg_left
    (coordinateExp_add_error D e hp hr hB.le hspeed x y hsmall) hL.le)
  rw [map_mul] at h
  exact h.trans_eq (by ring)

end DirectedCycles.GleasonLieAlgebra
