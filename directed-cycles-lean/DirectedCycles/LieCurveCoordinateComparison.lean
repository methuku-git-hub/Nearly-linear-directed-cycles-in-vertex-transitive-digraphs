import DirectedCycles.LieExponentialRadialControl

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- Inner exclusion and outer boundedness give an actual tangent annulus for
a one-parameter curve. Local exponential injectivity rules out distant
preimages in the upper bound. -/
theorem lie_curve_tangent_annulus {R ρ σ : ℝ} (hσ : 0 ≤ σ) (hσR : σ < R)
    (hinj : Set.InjOn (lieExponential (G := G) (E := E)) (Metric.ball 0 R))
    (φ : ℝ → G) (hφ0 : φ 0 = 1) (hφc : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) {v : E}
    (hφv : HasDerivAt (fun t => (chartAt E (1 : G)) (φ t)-(chartAt E (1 : G)) 1) v 0)
    (houter : ∀ t : ℝ, |t| ≤ 1 → φ t ∈ (lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) σ)
    (hinner : φ 1 ∉ (lieExponential (G := G) (E := E)) '' Metric.ball (0 : E) ρ) : ρ ≤ ‖v‖ ∧ ‖v‖ ≤ σ := by
  have heq := lie_one_parameter_eq_exponential φ hφ0 hφc hφadd hφv
  constructor
  · by_contra hh
    have hv : v ∈ Metric.ball 0 ρ := by simpa only [Metric.mem_ball,dist_zero_right] using lt_of_not_ge hh
    apply hinner
    exact ⟨v,hv,by simpa only [one_smul] using (heq 1).symm⟩
  · have hh := radial_norm_le_of_bounded_image (lieExponential (G := G)) hσ hσR
      (show (0 : ℝ) < 1 by norm_num) hinj v (fun t ht => by rw [← heq]; exact houter t ht)
    simpa only [one_mul] using hh

include hLie in
/-- Equality at one parameter value determines the whole curve when both
relevant tangent vectors lie in the proved injective exponential ball. -/
theorem lie_curve_coordinate_comparison {R : ℝ}
    (hinj : Set.InjOn (lieExponential (G := G) (E := E)) (Metric.ball 0 R))
    (φ ψ : ℝ → G) (hφ0 : φ 0 = 1) (hψ0 : ψ 0 = 1)
    (hφc : ContinuousAt φ 0) (hψc : ContinuousAt ψ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (hψadd : ∀ s t : ℝ, ψ (s+t) = ψ s*ψ t)
    {v w : E}
    (hφv : HasDerivAt (fun t => (chartAt E (1 : G)) (φ t)-(chartAt E (1 : G)) 1) v 0)
    (hψw : HasDerivAt (fun t => (chartAt E (1 : G)) (ψ t)-(chartAt E (1 : G)) 1) w 0)
    {t : ℝ} (he : φ 1 = ψ t) (hv : ‖v‖ < R) (htw : |t| * ‖w‖ < R) :
    v = t • w ∧ ∀ s : ℝ, φ s = ψ (t*s) := by
  have hφexp := lie_one_parameter_eq_exponential φ hφ0 hφc hφadd hφv
  have hψexp := lie_one_parameter_eq_exponential ψ hψ0 hψc hψadd hψw
  have hveq : v = t • w := by
    apply hinj
    · simpa only [Metric.mem_ball,dist_zero_right] using hv
    · simpa only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs] using htw
    · rw [hφexp 1,hψexp t,one_smul] at he
      exact he
  refine ⟨hveq,?_⟩
  intro s
  rw [hφexp,hψexp,hveq,smul_smul,mul_comm s t]
end DirectedCycles
