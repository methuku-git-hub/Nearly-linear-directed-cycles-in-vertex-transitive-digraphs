module

public import DirectedCycles.GleasonCoordinateSpeed
public import DirectedCycles.NormalizedPowerScale
public import Mathlib.Topology.Order.Compact

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

omit [FiniteDimensional ℝ E] in
theorem coordinateExp_nat_smul (n : ℕ) (x : E) :
    coordinateExp D e ((n : ℝ) • x) = (coordinateExp D e x)^n := by
  rw [coordinateExp_smul]
  have h := (toOneParameter D (e.symm x)).eval_nat_mul n 1
  change (toOneParameter D (e.symm x)).eval (n : ℝ) = ((toOneParameter D (e.symm x)).eval 1)^n
  simpa only [mul_one] using h

/-- Compactness of a coordinate annulus and exact integer powers give a
positive local lower bound for the group gauge of the actual exponential. -/
theorem exists_coordinateExp_lower_bound : ∃ c r : ℝ, 0 < c ∧ 0 < r ∧
    ∀ x : E, ‖x‖ ≤ r → c*‖x‖ ≤ D.gauge (coordinateExp D e x) := by
  classical
  have hS : (coordinateChart D e).source ∈ 𝓝 (0 : E) :=
    (coordinateChart D e).open_source.mem_nhds (zero_mem_coordinateChart_source D e)
  obtain ⟨δ,hδ,hδS⟩ := Metric.mem_nhds_iff.mp hS
  let ρ := δ/2
  have hρ : 0 < ρ := half_pos hδ
  let K : Set E := {x | ρ/2 ≤ ‖x‖ ∧ ‖x‖ ≤ ρ}
  have hK : IsCompact K := by
    apply (isCompact_closedBall (0 : E) ρ).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    intro x hx
    simpa only [Metric.mem_closedBall,dist_zero_right] using (show ‖x‖ ≤ ρ from hx.2)
  have hpos : ∀ x ∈ K, 0 < D.gauge (coordinateExp D e x) := by
    intro x hx
    apply lt_of_le_of_ne (D.gauge_nonneg _)
    intro hz
    have hexp : coordinateExp D e x = 1 := (D.gauge_eq_zero_iff _).mp hz.symm
    have hxS : x ∈ (coordinateChart D e).source := hδS (by
      rw [Metric.mem_ball,dist_zero_right]
      exact hx.2.trans_lt (by dsimp [ρ]; linarith))
    have hx0 : x = 0 := (coordinateChart D e).injOn hxS (zero_mem_coordinateChart_source D e) (by
      rw [coordinateChart_coe,hexp,coordinateExp_zero])
    have hn := hx.1
    rw [hx0,norm_zero] at hn
    linarith
  have hbound : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ D.gauge (coordinateExp D e x) := by
    by_cases hne : K.Nonempty
    · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hne
        (D.continuous_gauge.comp (continuous_coordinateExp D e)).continuousOn
      exact ⟨_,hpos x hx,hmin⟩
    · exact ⟨1,by norm_num,fun x hx => (hne ⟨x,hx⟩).elim⟩
  obtain ⟨m,hm,hmb⟩ := hbound
  refine ⟨m/ρ,ρ/2,div_pos hm hρ,half_pos hρ,?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp only [norm_zero,mul_zero,coordinateExp_zero,D.gauge_one,le_refl]
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let N : ℕ := ⌊ρ/‖x‖⌋₊
  have hb := normalized_power_scale_bounds hρ hnx hx
  change 0 < N ∧ ρ/2 ≤ (N : ℝ)*‖x‖ ∧ (N : ℝ)*‖x‖ ≤ ρ at hb
  have hmem : (N : ℝ) • x ∈ K := by
    change ρ/2 ≤ ‖(N : ℝ) • x‖ ∧ ‖(N : ℝ) • x‖ ≤ ρ
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg N)]
    exact hb.2
  have hmin := hmb _ hmem
  rw [coordinateExp_nat_smul] at hmin
  have hpow := D.gauge_pow_le (coordinateExp D e x) N
  have hmul := mul_le_mul_of_nonneg_right (hmin.trans hpow) hnx.le
  have hupper := mul_le_mul_of_nonneg_right hb.2.2 (D.gauge_nonneg (coordinateExp D e x))
  have heq : (m/ρ)*‖x‖ = (m*‖x‖)/ρ := by ring
  rw [heq]
  apply (div_le_iff₀ hρ).mpr
  nlinarith

end DirectedCycles.GleasonLieAlgebra
