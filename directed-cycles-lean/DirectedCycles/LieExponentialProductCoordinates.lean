module

public import DirectedCycles.LieExponentialStrictDerivative
public import DirectedCycles.LieExponentialContinuity
public import DirectedCycles.LieIdentityCoordinateMultiplication
public import DirectedCycles.LocalCoordinateChangeMultiplication
public import DirectedCycles.AdditionDerivativeNormBound

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- Actual exponential coordinates have a local multiplication with addition
derivative. Only the proved strict derivative and local inverse are used;
full smooth dependence of the exponential on its tangent is unnecessary. -/
theorem lie_exponential_product_coordinates :
    ∃ ν : E × E → E, ν (0,0) = 0 ∧
      HasFDerivAt ν (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (0,0) ∧
      ∀ᶠ p : E × E in 𝓝 (0,0), lieExponential (G := G) (ν p) =
        lieExponential p.1*lieExponential p.2 := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ,E)) (n := ∞)
  let e := chartAt E (1 : G)
  let c : E := e 1
  let F : E → E := fun v => e (lieExponential (G := G) v)-c
  let μ : E × E → E := fun p => e (e.symm (p.1+c)*e.symm (p.2+c))-c
  have h1 : (1 : G) ∈ e.source := mem_chart_source E 1
  have hF0 : F 0 = 0 := by simp only [F,lieExponential_zero,c,sub_self]
  have hF : HasStrictFDerivAt F (ContinuousLinearMap.id ℝ E) 0 :=
    lie_exponential_coordinate_strict_derivative (G := G) (E := E)
  obtain ⟨hμ,hl,hr,_⟩ := lie_group_identity_coordinate_multiplication (G := G) (E := E)
  obtain ⟨ν,hν0,hν,heq⟩ := local_coordinate_change_multiplication F hF0 hF μ
    (hμ.differentiableAt (by norm_num)) hl hr
  have hExp : Filter.Tendsto (lieExponential (G := G) (E := E)) (𝓝 0) (𝓝 (1 : G)) := by
    simpa only [lieExponential_zero] using (lie_exponential_continuous (G := G) (E := E)).continuousAt.tendsto (x := (0 : E))
  have hsource : ∀ᶠ v : E in 𝓝 0, lieExponential (G := G) v ∈ e.source :=
    hExp.eventually (e.open_source.mem_nhds h1)
  have hfst : Filter.Tendsto (fun p : E × E => p.1) (𝓝 (0,0)) (𝓝 (0 : E)) := continuousAt_fst
  have hsnd : Filter.Tendsto (fun p : E × E => p.2) (𝓝 (0,0)) (𝓝 (0 : E)) := continuousAt_snd
  have hνt : Filter.Tendsto ν (𝓝 (0,0)) (𝓝 (0 : E)) := by
    simpa only [hν0] using hν.continuousAt.tendsto
  have hprod : Filter.Tendsto (fun p : E × E => lieExponential (G := G) p.1*lieExponential p.2)
      (𝓝 (0,0)) (𝓝 (1 : G)) := by
    simpa only [one_mul,Function.comp_def] using (hExp.comp hfst).mul (hExp.comp hsnd)
  have hunchart : ∀ v : E, lieExponential (G := G) v ∈ e.source →
      e.symm (F v+c) = lieExponential (G := G) v := by
    intro v hv
    dsimp only [F]
    rw [sub_add_cancel]
    exact e.left_inv hv
  refine ⟨ν,hν0,hν,?_⟩
  filter_upwards [heq,hfst.eventually hsource,hsnd.eventually hsource,hνt.eventually hsource,
    hprod.eventually (e.open_source.mem_nhds h1)] with p hep hp1 hp2 hpn hpp
  apply e.injOn hpn hpp
  change e (lieExponential (G := G) (ν p))-c =
    e (e.symm (F p.1+c)*e.symm (F p.2+c))-c at hep
  rw [hunchart p.1 hp1,hunchart p.2 hp2] at hep
  exact sub_left_injective hep

include hLie in
/-- Products in sufficiently small exponential balls admit coordinates whose
norm is as close to the sum bound as prescribed. -/
theorem lie_exponential_product_norm_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ x y : E, ‖x‖ < r → ‖y‖ < r →
      ∃ z : E, ‖z‖ ≤ (1+ε)*(‖x‖+‖y‖) ∧
        lieExponential (G := G) z = lieExponential x*lieExponential y := by
  obtain ⟨ν,hν0,hν,heq⟩ := lie_exponential_product_coordinates (G := G) (E := E)
  obtain ⟨a,ha,habound⟩ := addition_derivative_norm_bound ν hν0 hν hε
  obtain ⟨b,hb,hbeq⟩ := Metric.mem_nhds_iff.mp heq
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro x y hx hy
  refine ⟨ν (x,y),habound x y (hx.trans_le (min_le_left _ _)) (hy.trans_le (min_le_left _ _)),?_⟩
  apply hbeq
  simp only [Metric.mem_ball,Prod.dist_eq,dist_zero_right]
  exact max_lt (hx.trans_le (min_le_right _ _)) (hy.trans_le (min_le_right _ _))
end DirectedCycles
