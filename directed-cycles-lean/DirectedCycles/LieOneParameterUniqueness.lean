import DirectedCycles.LieIdentityCoordinateMultiplication
import DirectedCycles.LocalMultiplicativeCurveUniqueness
import DirectedCycles.OneParameterGermUniqueness
import DirectedCycles.GroupCurveCoordinateLaw

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- The identity-coordinate tangent uniquely determines an actual continuous
one-parameter subgroup of a smooth real Lie group. -/
theorem lie_group_one_parameter_unique (φ ψ : ℝ → G)
    (hφ0 : φ 0 = 1) (hψ0 : ψ 0 = 1) (hφc : ContinuousAt φ 0) (hψc : ContinuousAt ψ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (hψadd : ∀ s t : ℝ, ψ (s+t) = ψ s*ψ t)
    {v : E}
    (hφv : HasDerivAt (fun t => (chartAt E (1 : G)) (φ t)-(chartAt E (1 : G)) 1) v 0)
    (hψv : HasDerivAt (fun t => (chartAt E (1 : G)) (ψ t)-(chartAt E (1 : G)) 1) v 0) : φ = ψ := by
  let e := chartAt E (1 : G)
  let c : E := e 1
  let chart : G → E := fun x => e x-c
  let unchart : E → G := fun y => e.symm (y+c)
  let μ : E × E → E := fun p => chart (unchart p.1*unchart p.2)
  have h1 : (1 : G) ∈ e.source := mem_chart_source E 1
  have hV : e.source ∈ 𝓝 (1 : G) := e.open_source.mem_nhds h1
  have hleft : ∀ x ∈ e.source, unchart (chart x) = x := by
    intro x hx
    dsimp only [unchart,chart]
    rw [sub_add_cancel]
    exact e.left_inv hx
  obtain ⟨hμ,_,_,_⟩ := lie_group_identity_coordinate_multiplication (G := G) (E := E)
  obtain ⟨r,hr,hφlaw⟩ := group_curve_coordinate_local_law chart unchart e.source hV hleft φ hφ0 hφc hφadd
  obtain ⟨s,hs,hψlaw⟩ := group_curve_coordinate_local_law chart unchart e.source hV hleft ψ hψ0 hψc hψadd
  have hf0 : chart (φ 0) = 0 := by dsimp only [chart,c]; rw [hφ0,sub_self]
  have hg0 : chart (ψ 0) = 0 := by dsimp only [chart,c]; rw [hψ0,sub_self]
  have hnear := local_multiplicative_curve_eventually_unique μ (hμ.of_le (by simp))
    (fun t => chart (φ t)) (fun t => chart (ψ t)) hf0 hg0 hφv hψv hr hs hφlaw hψlaw
  apply one_parameter_eq_of_eventually_eq φ ψ hφ0 hψ0 hφadd hψadd
  have hφnear : ∀ᶠ t : ℝ in 𝓝 0, φ t ∈ e.source := hφc.preimage_mem_nhds (by simpa only [hφ0] using hV)
  have hψnear : ∀ᶠ t : ℝ in 𝓝 0, ψ t ∈ e.source := hψc.preimage_mem_nhds (by simpa only [hψ0] using hV)
  filter_upwards [hnear,hφnear,hψnear] with t he hφ hψ
  rw [← hleft _ hφ,he,hleft _ hψ]
end DirectedCycles
