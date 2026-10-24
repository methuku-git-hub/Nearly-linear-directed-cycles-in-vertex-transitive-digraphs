import DirectedCycles.LieOneParameterCoordinateDerivative
import DirectedCycles.OneParameterLocalTriviality

set_option autoImplicit false
open scoped Topology Manifold ContDiff
open IsManifold
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) 2 G]

include hLie in
/-- A nontrivial continuous one-parameter homomorphism in a C2 Banach Lie group
has a nonzero tangent. The quadratic estimate rules out a zero tangent without
assuming uniqueness for an unconstructed differential equation. -/
theorem lieGroup_one_parameter_nonzero_derivative
    (φ : ℝ → G) (hφ0 : φ 0 = 1) (hφcont : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (hnt : ∃ t : ℝ, φ t ≠ 1) :
    ∃ v : E, v ≠ 0 ∧
      HasDerivAt (fun t => (chartAt E (1 : G)) (φ t)-(chartAt E (1 : G)) 1) v 0 := by
  obtain ⟨v,hv,K,hK,herr⟩ := lieGroup_one_parameter_coordinate_derivative (E := E) φ hφ0 hφcont hφadd
  refine ⟨v,?_,hv⟩
  intro hv0
  let e := chartAt E (1 : G)
  let f : ℝ → E := fun t => e (φ t)-e 1
  have h1 : (1 : G) ∈ e.source := mem_chart_source E 1
  have hf0 : f 0 = 0 := by simp only [f,hφ0,sub_self]
  have hfcont : ContinuousAt f 0 := by
    have hecont : ContinuousAt e (φ 0) := by simpa only [hφ0] using e.continuousAt h1
    exact (hecont.comp hφcont).sub continuousAt_const
  have hn : Filter.Tendsto (fun t => K*‖f t‖) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [hf0,norm_zero,mul_zero] using hfcont.norm.tendsto.const_mul K
  have hsmall : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), K*‖f t‖ < 1 :=
    hn.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1))
  have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), φ t ∈ e.source :=
    hφcont.preimage_mem_nhds (by simpa only [hφ0] using e.open_source.mem_nhds h1)
  have hone : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), φ t = 1 := by
    filter_upwards [herr,hsmall,hnear] with t he hs ht
    have he' : ‖f t‖ ≤ K*‖f t‖^2 := by simpa only [hv0,smul_zero,sub_zero] using he
    have hz : ‖f t‖ = 0 := by
      by_contra hz
      have hp : 0 < ‖f t‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have hh := mul_lt_mul_of_pos_right hs hp
      nlinarith
    have hf : f t = 0 := norm_eq_zero.1 hz
    apply e.injOn ht h1
    exact sub_eq_zero.1 hf
  obtain ⟨t,ht⟩ := hnt
  exact ht (one_parameter_trivial_of_eventually_one φ hφ0 hφadd hone t)
end DirectedCycles
