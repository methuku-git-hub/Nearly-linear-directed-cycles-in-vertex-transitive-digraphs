import DirectedCycles.GleasonAdjointBounds
import DirectedCycles.GleasonExponentialConjugateFactors
import DirectedCycles.GleasonExponentialProducts

set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- The actual left group difference is quadratically approximated by the
exponential of the averaged adjoint applied to the coordinate difference.
The estimate is obtained from finite conjugate products and their limits. -/
theorem coordinateExp_averaged_difference_error : ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧
    ∀ x y : E, ‖x‖ ≤ δ → ‖y‖ ≤ δ →
      D.metric.dist ((coordinateExp D e x)⁻¹*coordinateExp D e y)
        (coordinateExp D e (coordinateAdjointAverage D e y (y-x))) ≤ K*‖y-x‖^2 := by
  let : MetricSpace G := D.compatibleMetric
  obtain ⟨A,hA,hspeed⟩ := exists_coordinate_speed D e
  obtain ⟨r,_hr,hrC,hp⟩ := D.exists_trotter_radius
  obtain ⟨Kp,ρ,hKp,hρ,hprod⟩ := exists_coordinateExp_ordered_product_bound D e
  obtain ⟨M,σ,hM,hσ,hbound⟩ := exists_coordinateAdjoint_radial_bound D e
  let δ := min σ (min (r/(2*A)) (ρ/(2*M)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨Kp*M^2,δ,by positivity,hδ,?_⟩
  intro x y hx hy
  have hyσ : ‖y‖ ≤ σ := hy.trans (min_le_left _ _)
  have hδr : δ ≤ r/(2*A) := (min_le_right _ _).trans (min_le_left _ _)
  have hδρ : δ ≤ ρ/(2*M) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : A*(‖x‖+‖y‖) ≤ r := by
    have hh := (le_div_iff₀ (show 0 < 2*A by positivity)).mp hδr
    nlinarith
  have hz : M*‖y-x‖ ≤ ρ := by
    have hh := (le_div_iff₀ (show 0 < 2*M by positivity)).mp hδρ
    have hh' := mul_le_mul_of_nonneg_left (norm_sub_le y x) hM.le
    nlinarith
  let v (n k : ℕ) : E := (1/(n : ℝ)) •
    coordinateAdjoint D e (coordinateExp D e ((-((k : ℝ)/n)) • y)) (y-x)
  let S (n : ℕ) : E := ∑ k ∈ Finset.range n, v n k
  let P (n : ℕ) : G := ((List.range n).map (fun k => coordinateExp D e (v n k))).prod
  let g := (coordinateExp D e x)⁻¹*coordinateExp D e y
  let B := 16*D.constant*A^2*‖x‖*‖y‖
  have hv (n : ℕ) (hn : 0 < n) : (∑ k ∈ Finset.range n, ‖v n k‖) ≤ M*‖y-x‖ :=
    coordinateAdjoint_riemann_variation_bound D e hbound y (y-x) hyσ n hn
  have he (n : ℕ) (hn : 0 < n) :
      D.metric.dist g (coordinateExp D e (S n)) ≤ B/(n : ℝ)+(Kp*M^2)*‖y-x‖^2 := by
    have h₁ : D.metric.dist g (P n) ≤ B/(n : ℝ) :=
      coordinateExp_discrete_adjoint_error D e hp hrC hA.le hspeed x y hsmall n hn
    have h₂ : D.metric.dist (P n) (coordinateExp D e (S n)) ≤ Kp*(∑ k ∈ Finset.range n, ‖v n k‖)^2 :=
      hprod (v n) n ((hv n hn).trans hz)
    have hsq := mul_self_le_mul_self (Finset.sum_nonneg (fun k _ => norm_nonneg (v n k))) (hv n hn)
    have hsq' : (∑ k ∈ Finset.range n, ‖v n k‖)^2 ≤ (M*‖y-x‖)^2 := by simpa only [pow_two] using hsq
    have h₂' := h₂.trans (mul_le_mul_of_nonneg_left hsq' hKp.le)
    exact (D.metric.dist_triangle g (P n) (coordinateExp D e (S n))).trans
      ((add_le_add h₁ h₂').trans_eq (by dsimp [B]; ring))
  have hS : Tendsto S atTop (𝓝 (coordinateAdjointAverage D e y (y-x))) :=
    coordinateAdjointAverage_riemann_apply_tendsto D e y (y-x)
  have hF := ((continuous_coordinateExp D e).tendsto _).comp hS
  have hdist : Tendsto (fun n => D.metric.dist g (coordinateExp D e (S n))) atTop
      (𝓝 (D.metric.dist g (coordinateExp D e (coordinateAdjointAverage D e y (y-x))))) :=
    tendsto_const_nhds.dist hF
  have hB : Tendsto (fun n : ℕ => B/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul B
  have hright : Tendsto (fun n : ℕ => B/(n : ℝ)+(Kp*M^2)*‖y-x‖^2) atTop
      (𝓝 ((Kp*M^2)*‖y-x‖^2)) := by
    simpa only [zero_add] using hB.add_const ((Kp*M^2)*‖y-x‖^2)
  apply le_of_tendsto_of_tendsto hdist hright
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact he n hn

end DirectedCycles.GleasonLieAlgebra
