module

public import DirectedCycles.ParameterIntegralCurveLipschitz

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The zero-parameter trajectory is constant, so the common parameter
Lipschitz estimate bounds the size of every trajectory uniformly in time. -/
theorem parameter_integral_curve_norm_bound (A : E → E →L[ℝ] E) (f : E × ℝ → E)
    {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) (K : NNReal)
    (hder : ∀ v : E, ‖v‖ ≤ r → f (v,0) = 0 ∧ ∀ t : ℝ, |t| < ε →
      HasDerivAt (fun t => f (v,t)) (A (f (v,t)) v) t)
    (hLip : ∀ t : ℝ, |t| < ε → LipschitzOnWith K (fun v => f (v,t)) (Metric.closedBall 0 r)) :
    (∀ t : ℝ, |t| < ε → f (0,t) = 0) ∧
      ∀ v : E, ‖v‖ ≤ r → ∀ t : ℝ, |t| < ε → ‖f (v,t)‖ ≤ (K : ℝ)*‖v‖ := by
  have h0 : ‖(0 : E)‖ ≤ r := by simpa only [norm_zero] using hr
  have hz : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by constructor <;> linarith
  have hzero : ∀ t : ℝ, |t| < ε → f (0,t) = 0 := by
    intro t ht
    have hd : ∀ s ∈ Set.Ioo (-ε) ε, HasDerivAt (fun s => f (0,s)) (0 : E) s := by
      intro s hs
      simpa only [map_zero] using (hder 0 h0).2 s (abs_lt.mpr hs)
    have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-ε) ε).isPreconnected
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) (abs_lt.mp ht) hz
    rw [(hder 0 h0).1] at he
    exact he
  refine ⟨hzero,?_⟩
  intro v hv t ht
  have hvB : v ∈ Metric.closedBall 0 r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  have hh := (hLip t ht).dist_le_mul v hvB 0 (Metric.mem_closedBall_self hr)
  simpa only [hzero t ht,dist_zero_right] using hh
end DirectedCycles
