import DirectedCycles.DiscreteRadialNormControl
import DirectedCycles.LieExponentialContinuity

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ,E) ∞ G]

/-- Consecutive actual group powers in a small exponential ball give the
exact reciprocal bound on the original tangent coordinate. -/
theorem lie_exponential_finite_power_control {R ρ : ℝ} (hρ : 0 ≤ ρ) (hR : 2*ρ < R)
    (hinj : Set.InjOn (lieExponential (G := G) (E := E)) (Metric.ball 0 R))
    {x : G} (hx : x ∈ (lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) ρ)
    (N : ℕ) (hp : ∀ n ≤ N, x^n ∈ (lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) ρ) :
    ∃ v : E, lieExponential (G := G) v = x ∧ ‖v‖ ≤ ρ ∧ (N : ℝ)*‖v‖ ≤ ρ := by
  obtain ⟨v,hv,rfl⟩ := hx
  have hvn : ‖v‖ ≤ ρ := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  refine ⟨v,rfl,hvn,?_⟩
  apply discrete_radial_norm_le (lieExponential (G := G)) hρ hR hinj v hvn N
  intro n hn
  rw [lieExponential_nat_smul]
  exact hp n hn

/-- A sufficiently long finite power test forces membership in an inner
exponential ball, with no assumed global logarithm or path of intermediate powers. -/
theorem lie_exponential_inner_of_finite_powers {R ρ σ : ℝ} (hρ : 0 ≤ ρ) (hR : 2*ρ < R)
    (hinj : Set.InjOn (lieExponential (G := G) (E := E)) (Metric.ball 0 R))
    {x : G} (hx : x ∈ (lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) ρ)
    (N : ℕ) (hN : 0 < N) (hσ : ρ < (N : ℝ)*σ)
    (hp : ∀ n ≤ N, x^n ∈ (lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) ρ) :
    x ∈ (lieExponential (G := G) (E := E)) '' Metric.ball (0 : E) σ := by
  obtain ⟨v,he,_,hv⟩ := lie_exponential_finite_power_control hρ hR hinj hx N hp
  refine ⟨v,?_,he⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlt : ‖v‖ < σ := (mul_lt_mul_iff_right₀ hNpos).1 (hv.trans_lt hσ)
  simpa only [Metric.mem_ball,dist_zero_right] using hlt
end DirectedCycles
