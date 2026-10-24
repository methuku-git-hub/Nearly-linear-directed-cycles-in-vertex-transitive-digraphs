import DirectedCycles.LieUniformExponentialCurves

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- The actual exponential is continuous at every point of a constructed open
neighbourhood of zero, by the jointly continuous ODE realization. -/
theorem lie_exponential_continuous_neighbourhood :
    ∃ U : Set E, IsOpen U ∧ (0 : E) ∈ U ∧ ∀ v ∈ U, ContinuousAt (lieExponential (G := G)) v := by
  obtain ⟨γ,D,hDo,hD0,hγD,R,r,hR,hr,hreal⟩ := lie_uniform_exponential_curves (G := G) (E := E)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hDo.mem_nhds hD0)
  let τ := min r δ/2
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτr : τ ≤ r := by have := min_le_left r δ; have := lt_min hr hδ; dsimp only [τ]; linarith
  have hτδ : τ < δ := by have := min_le_right r δ; dsimp only [τ]; linarith
  have htime : |τ| ≤ r := by rw [abs_of_pos hτ]; exact hτr
  have hbase : ((0 : E),τ) ∈ D := hball (show ((0 : E),τ) ∈ Metric.ball (0,0) δ from by
    simp only [Metric.mem_ball,Prod.dist_eq,dist_self,Real.dist_eq,sub_zero,abs_of_pos hτ,max_eq_right hτ.le]
    exact hτδ)
  let k : E → E × ℝ := fun v => (τ⁻¹ • v,τ)
  have hk : Continuous k := (continuous_const.smul continuous_id).prodMk continuous_const
  let U : Set E := k ⁻¹' D ∩ (fun v : E => τ⁻¹ • v) ⁻¹' Metric.ball 0 R
  have hUo : IsOpen U := (hDo.preimage hk).inter (Metric.isOpen_ball.preimage (continuous_const.smul continuous_id))
  have hU0 : (0 : E) ∈ U := by
    constructor
    · simpa only [Set.mem_preimage,k,smul_zero] using hbase
    · simpa only [Set.mem_preimage,smul_zero] using Metric.mem_ball_self hR
  have heq : ∀ v ∈ U, lieExponential (G := G) v = γ (k v) := by
    intro v hv
    have hvR : ‖τ⁻¹ • v‖ < R := by simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hv.2
    have he := hreal (τ⁻¹ • v) hvR τ htime
    simpa only [k,smul_smul,mul_inv_cancel₀ hτ.ne',one_smul] using he.symm
  refine ⟨U,hUo,hU0,?_⟩
  intro v hv
  have hcont : ContinuousAt (fun w => γ (k w)) v :=
    (hγD.continuousAt (hDo.mem_nhds hv.1)).comp hk.continuousAt
  apply hcont.congr_of_eventuallyEq
  filter_upwards [hUo.mem_nhds hv] with w hw
  exact heq w hw

/-- Integer scaling of a tangent is the corresponding genuine group power. -/
theorem lieExponential_nat_smul (v : E) (n : ℕ) :
    lieExponential (G := G) ((n : ℝ) • v) = (lieExponential v)^n := by
  induction n with
  | zero => simp only [Nat.cast_zero,zero_smul,lieExponential_zero,pow_zero]
  | succ n ih =>
    rw [Nat.cast_succ,lieExponential_add_line,ih,one_smul,pow_succ]

include hLie in
/-- The exponential is continuous on the whole identity-coordinate tangent
space. Integer subdivision reduces every point to the proved neighbourhood. -/
theorem lie_exponential_continuous : Continuous (lieExponential (G := G) (E := E)) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ,E)) (n := ∞)
  obtain ⟨U,hUo,hU0,hU⟩ := lie_exponential_continuous_neighbourhood (G := G) (E := E)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hU0)
  apply continuous_iff_continuousAt.2
  intro v
  obtain ⟨n,hn⟩ := exists_nat_gt (‖v‖/δ+1)
  have hnR : (0 : ℝ) < n := by have := div_nonneg (norm_nonneg v) hδ.le; linarith
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hscaled : ‖((n : ℝ)⁻¹) • v‖ < δ := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hnR]
    rw [← div_eq_inv_mul]
    apply (div_lt_iff₀ hnR).2
    have hh := (div_lt_iff₀ hδ).1 (show ‖v‖/δ < (n : ℝ) by linarith)
    nlinarith
  have hvU : ((n : ℝ)⁻¹) • v ∈ U := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hscaled)
  have hcont : ContinuousAt (fun w : E => (lieExponential (G := G) (((n : ℝ)⁻¹) • w))^n) v :=
    ((hU _ hvU).comp (continuousAt_const.smul continuousAt_id)).pow n
  have he : (fun w : E => (lieExponential (G := G) (((n : ℝ)⁻¹) • w))^n) = lieExponential := by
    funext w
    rw [← lieExponential_nat_smul,smul_smul,mul_inv_cancel₀ hn0,one_smul]
  rwa [he] at hcont
end DirectedCycles
