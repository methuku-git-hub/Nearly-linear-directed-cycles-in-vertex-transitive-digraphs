module

public import DirectedCycles.LieExponentialStrictDerivative
public import DirectedCycles.LieExponentialContinuity
public import DirectedCycles.LieIdentityCoordinateConjugation
public import DirectedCycles.IdentityDerivativeNormBounds

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- Actual conjugation of small exponential values has coordinates bounded
linearly by the conjugated vector, uniformly in the conjugating vector. -/
theorem lie_exponential_conjugation_norm_bound :
    ∃ r : ℝ, 0 < r ∧ ∀ x y : E, ‖x‖ < r → ‖y‖ < r →
      ∃ z : E, ‖z‖ ≤ 4*‖y‖ ∧ lieExponential (G := G) z =
        lieExponential x*lieExponential y*(lieExponential x)⁻¹ := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ,E)) (n := ∞)
  let e := chartAt E (1 : G)
  let c : E := e 1
  let F : E → E := fun v => e (lieExponential (G := G) v)-c
  let χ : E × E → E := fun p => e (e.symm (p.1+c)*e.symm (p.2+c)*(e.symm (p.1+c))⁻¹)-c
  have h1 : (1 : G) ∈ e.source := mem_chart_source E 1
  have hF0 : F 0 = 0 := by simp only [F,lieExponential_zero,c,sub_self]
  have hF : HasStrictFDerivAt F (ContinuousLinearMap.id ℝ E) 0 :=
    lie_exponential_coordinate_strict_derivative (G := G) (E := E)
  obtain ⟨β,hβ0,hβ,hright,_⟩ := strict_identity_local_inverse F hF0 hF
  obtain ⟨rF,hrF,hFnorm⟩ := identity_derivative_norm_bounds F hF0 hF.hasFDerivAt (show (0 : ℝ) < 1/10 by norm_num)
  obtain ⟨rβ,hrβ,hβnorm⟩ := identity_derivative_norm_bounds β hβ0 hβ (show (0 : ℝ) < 1/10 by norm_num)
  obtain ⟨hχ,hχleft,_⟩ := lie_group_identity_coordinate_conjugation (G := G) (E := E)
  obtain ⟨a,ha,hχnorm⟩ := lie_identity_conjugation_norm_bound (G := G) (E := E)
  have hχ0 : χ (0,0) = 0 := hχleft.self_of_nhds
  let θ : E × E → E := fun p => χ (F p.1,F p.2)
  have hθ0 : θ (0,0) = 0 := by simp only [θ,hF0,hχ0]
  have hχ' : ContinuousAt χ (F 0,F 0) := by simpa only [hF0] using hχ.continuousAt
  have hFfst : ContinuousAt (fun p : E × E => F p.1) (0,0) :=
    hF.continuousAt.tendsto.comp
      (show Filter.Tendsto (fun p : E × E => p.1) (𝓝 ((0 : E),0)) (𝓝 0) from continuousAt_fst)
  have hFsnd : ContinuousAt (fun p : E × E => F p.2) (0,0) :=
    hF.continuousAt.tendsto.comp
      (show Filter.Tendsto (fun p : E × E => p.2) (𝓝 ((0 : E),0)) (𝓝 0) from continuousAt_snd)
  have hθc : ContinuousAt θ (0,0) :=
    hχ'.tendsto.comp (hFfst.prodMk hFsnd).tendsto
  have hθt : Filter.Tendsto θ (𝓝 (0,0)) (𝓝 (0 : E)) := by simpa only [hθ0] using hθc.tendsto
  let κ : E × E → E := fun p => β (θ p)
  have hβ' : ContinuousAt β (θ (0,0)) := by simpa only [hθ0] using hβ.continuousAt
  have hκt : Filter.Tendsto κ (𝓝 (0,0)) (𝓝 (0 : E)) := by
    simpa only [Function.comp_def,κ,hθ0,hβ0] using (hβ'.comp hθc).tendsto
  have hExp : Filter.Tendsto (lieExponential (G := G) (E := E)) (𝓝 0) (𝓝 (1 : G)) := by
    simpa only [lieExponential_zero] using (lie_exponential_continuous (G := G) (E := E)).continuousAt.tendsto (x := (0 : E))
  have hsource : ∀ᶠ v : E in 𝓝 0, lieExponential (G := G) v ∈ e.source :=
    hExp.eventually (e.open_source.mem_nhds h1)
  have hfst : Filter.Tendsto (fun p : E × E => p.1) (𝓝 (0,0)) (𝓝 (0 : E)) := continuousAt_fst
  have hsnd : Filter.Tendsto (fun p : E × E => p.2) (𝓝 (0,0)) (𝓝 (0 : E)) := continuousAt_snd
  have hconj : Filter.Tendsto (fun p : E × E => lieExponential (G := G) p.1*lieExponential p.2*(lieExponential p.1)⁻¹)
      (𝓝 (0,0)) (𝓝 (1 : G)) := by
    simpa only [one_mul,inv_one,Function.comp_def] using
      ((hExp.comp hfst).mul (hExp.comp hsnd)).mul (hExp.comp hfst).inv
  have hFsmall : ∀ᶠ v : E in 𝓝 0, ‖F v‖ < a :=
    hF.continuousAt.norm.preimage_mem_nhds (Iio_mem_nhds (by simpa only [hF0,norm_zero] using ha))
  have hθsmall : ∀ᶠ p : E × E in 𝓝 (0,0), ‖θ p‖ < rβ := by
    filter_upwards [hθt.eventually (Metric.ball_mem_nhds (0 : E) hrβ)] with p hp
    simpa only [Metric.mem_ball,dist_zero_right] using hp
  have hunchart : ∀ v : E, lieExponential (G := G) v ∈ e.source →
      e.symm (F v+c) = lieExponential (G := G) v := by
    intro v hv
    dsimp only [F]
    rw [sub_add_cancel]
    exact e.left_inv hv
  have hgood : ∀ᶠ p : E × E in 𝓝 (0,0), ‖κ p‖ ≤ 4*‖p.2‖ ∧
      lieExponential (G := G) (κ p) = lieExponential p.1*lieExponential p.2*(lieExponential p.1)⁻¹ := by
    filter_upwards [hfst.eventually hFsmall,hsnd.eventually hFsmall,hθsmall,
      hsnd.eventually (Metric.ball_mem_nhds (0 : E) hrF),hθt.eventually hright,
      hfst.eventually hsource,hsnd.eventually hsource,hκt.eventually hsource,
      hconj.eventually (e.open_source.mem_nhds h1)] with p hp1 hp2 hθp hpF he hs1 hs2 hsκ hsc
    have hFp : ‖p.2‖ < rF := by simpa only [Metric.mem_ball,dist_zero_right] using hpF
    have hb : ‖κ p‖ ≤ (1+1/10 : ℝ)*‖θ p‖ := (hβnorm (θ p) hθp).2
    have hc : ‖θ p‖ ≤ 2*‖F p.2‖ := hχnorm (F p.1) (F p.2) hp1 hp2
    have hf := (hFnorm p.2 hFp).2
    refine ⟨by nlinarith [norm_nonneg p.2],?_⟩
    apply e.injOn hsκ hsc
    change e (lieExponential (G := G) (κ p))-c =
      e (e.symm (F p.1+c)*e.symm (F p.2+c)*(e.symm (F p.1+c))⁻¹)-c at he
    rw [hunchart p.1 hs1,hunchart p.2 hs2] at he
    exact sub_left_injective he
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨r,hr,?_⟩
  intro x y hx hy
  exact ⟨κ (x,y),hball (by simpa only [Metric.mem_ball,Prod.dist_eq,dist_zero_right] using max_lt hx hy)⟩
end DirectedCycles
