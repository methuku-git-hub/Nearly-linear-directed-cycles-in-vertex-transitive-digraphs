import DirectedCycles.GleasonNormedHomBound

set_option autoImplicit false
namespace DirectedCycles.GleasonMetricData
variable {G A : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [NormedRing A] [NormedAlgebra ℝ A]

/-- The identity gauge bound upgrades to a two-point local Lipschitz
bound using the actual homomorphism identity. -/
theorem continuous_hom_locally_lipschitz (F : ContinuousMonoidHom G A) :
    ∃ L r : ℝ, 0 < L ∧ 0 < r ∧ ∀ a b : G,
      D.gauge a ≤ r → D.gauge b ≤ r → ‖F a-F b‖ ≤ L*D.metric.dist a b := by
  obtain ⟨L,r,hL,hr,hbound⟩ := D.continuous_hom_gauge_bound F
  let s := min (r/2) (1/L)
  have hs : 0 < s := lt_min (half_pos hr) (one_div_pos.mpr hL)
  have hM : 0 < ‖(1 : A)‖+1 := by positivity
  refine ⟨(‖(1 : A)‖+1)*L,s,mul_pos hM hL,hs,?_⟩
  intro a b ha hb
  have has : D.gauge a ≤ r := ha.trans ((min_le_left _ _).trans (by linarith))
  have hLb : L*D.gauge a ≤ 1 := by
    have h := (le_div_iff₀ hL).mp (ha.trans (min_le_right _ _))
    nlinarith
  have hFa : ‖F a‖ ≤ ‖(1 : A)‖+1 := by
    have hnorm := norm_add_le (F a-1) (1 : A)
    rw [sub_add_cancel] at hnorm
    have h := (hbound a has).trans hLb
    linarith
  have hab : D.gauge (a⁻¹*b) ≤ r := by
    have h := D.gauge_mul_le a⁻¹ b
    rw [D.gauge_inv] at h
    have hs₀ := min_le_left (r/2) (1/L)
    dsimp only [s] at ha hb
    linarith
  have heq : F b-F a = F a*(F (a⁻¹*b)-1) := by
    rw [mul_sub,mul_one,← map_mul]
    simp only [mul_inv_cancel_left]
  rw [norm_sub_rev,heq]
  have h := (norm_mul_le (F a) (F (a⁻¹*b)-1)).trans
    (mul_le_mul hFa (hbound _ hab) (norm_nonneg _) hM.le)
  rw [← D.dist_eq_gauge] at h
  exact h.trans_eq (by ring)

end DirectedCycles.GleasonMetricData
