import DirectedCycles.LieExponentialCurve

set_option autoImplicit false
open scoped Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ,E) ∞ G]

theorem lieExponential_neg (v : E) :
    lieExponential (G := G) (-v) = (lieExponential v)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have h := lieExponential_add_line (G := G) v (-1) 1
  simpa only [neg_add_cancel,zero_smul,lieExponential_zero,neg_one_smul,one_smul] using h.symm

theorem lie_exponential_closedBall_inv_mem {ρ : ℝ} {x : G}
    (hx : x ∈ (lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) ρ) :
    x⁻¹ ∈ (lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) ρ := by
  obtain ⟨v,hv,rfl⟩ := hx
  refine ⟨-v,?_,lieExponential_neg v⟩
  simpa only [Metric.mem_closedBall,dist_zero_right,norm_neg] using hv
end DirectedCycles
