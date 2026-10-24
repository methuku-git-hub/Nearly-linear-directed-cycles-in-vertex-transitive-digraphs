import DirectedCycles.LocalExponentialCurveGerm
import DirectedCycles.LocalRadialRestrictedNormControl

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
namespace LocalExponentialData
variable {H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [ChartedSpace E H] {Q : LocalGroupAlgebra H}
    (D : LocalExponentialData (E := E) Q)

/-- A bounded actual local curve has an exponential tangent in the exact
annulus prescribed by the inner exclusion and outer closed ball. Agreement
with exponential coordinates is proved on the whole closed unit interval. -/
theorem curve_annulus (hQ : LocalGroupSmoothness (E := E) Q)
    (f : ℝ → H) (hf0 : f 0 = Q.one) (hfc : ContinuousAt f 0)
    (hfadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t)))
    {ρ σ : ℝ} (hσ : 0 ≤ σ) (hσR : σ < D.radius)
    (houter : ∀ t : ℝ, |t| ≤ 1 → f t ∈ D.chart '' Metric.closedBall (0 : E) σ)
    (hinner : f 1 ∉ D.chart '' Metric.ball (0 : E) ρ) :
    ∃ v : E, HasDerivAt (fun t => D.baseChart.symm (f t)) v 0 ∧
      (ρ ≤ ‖v‖ ∧ ‖v‖ ≤ σ) ∧ ∀ t : ℝ, |t| ≤ 1 → f t = D.chart (t • v) := by
  obtain ⟨v,hv,hnear⟩ := D.curve_germ hQ f hf0 hfc hfadd
  have hvσ : ‖v‖ ≤ σ := by
    have hh := radial_norm_le_of_locally_bounded_image D.chart hσ hσR
      (by norm_num : (0 : ℝ) < 1) (D.chart.injOn.mono D.ball_source) v
      (fun t ht htv => by rw [← D.curve_eq_of_germ f hf0 hfadd v hnear t ht htv]; exact houter t ht)
    simpa only [one_mul] using hh
  have heq : ∀ t : ℝ, |t| ≤ 1 → f t = D.chart (t • v) := by
    intro t ht
    apply D.curve_eq_of_germ f hf0 hfadd v hnear t ht
    exact (mul_le_mul_of_nonneg_right ht (norm_nonneg v)).trans_lt
      (by simpa only [one_mul] using hvσ.trans_lt hσR)
  refine ⟨v,hv,⟨?_,hvσ⟩,heq⟩
  by_contra hh
  apply hinner
  refine ⟨v,?_,?_⟩
  · simpa only [Metric.mem_ball,dist_zero_right] using lt_of_not_ge hh
  · simpa only [one_smul] using (heq 1 (by norm_num)).symm
end LocalExponentialData
end DirectedCycles
