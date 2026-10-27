module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- One finite cover of a fixed compact ball rescales to every positive
radius, so its cardinality is independent of the eventual source scale. -/
theorem uniform_scaled_ball_cover (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset E, ∀ r : ℝ, 0 < r → ∀ v : E, ‖v‖ ≤ C*r →
      ∃ c ∈ F, ‖v-r • c‖ < ε*r := by
  classical
  obtain ⟨T,_,hTf,hT⟩ := (isCompact_closedBall (0 : E) C).finite_cover_balls hε
  refine ⟨hTf.toFinset,?_⟩
  intro r hr v hv
  have hv' : r⁻¹ • v ∈ Metric.closedBall (0 : E) C := by
    simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
    exact (inv_mul_le_iff₀ hr).2 (by nlinarith)
  obtain ⟨c,hc,hvc⟩ := Set.mem_iUnion₂.mp (hT hv')
  have hdist : ‖r⁻¹ • v-c‖ < ε := by simpa only [Metric.mem_ball,dist_eq_norm] using hvc
  refine ⟨c,hTf.mem_toFinset.mpr hc,?_⟩
  have he : r • (r⁻¹ • v-c) = v-r • c := by
    rw [smul_sub,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  rw [← he,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  nlinarith
end DirectedCycles
