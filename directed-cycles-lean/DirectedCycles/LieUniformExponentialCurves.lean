import DirectedCycles.LocalLieCurveExponential
import DirectedCycles.UniformLocalOneParameterExistence

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- The actual exponential curves have a jointly continuous realization on
an open neighbourhood, with a common time interval for all small tangents. -/
theorem lie_uniform_exponential_curves :
    ∃ γ : E × ℝ → G, ∃ D : Set (E × ℝ), IsOpen D ∧ (0,0) ∈ D ∧ ContinuousOn γ D ∧
      ∃ R r : ℝ, 0 < R ∧ 0 < r ∧ ∀ v : E, ‖v‖ < R →
        ∀ t : ℝ, |t| ≤ r → γ (v,t) = lieExponential (G := G) (t • v) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ,E)) (n := ∞)
  let e := chartAt E (1 : G)
  let c : E := e 1
  let chart : G → E := fun x => e x-c
  let unchart : E → G := fun y => e.symm (y+c)
  let μ : E × E → E := fun p => chart (unchart p.1*unchart p.2)
  have h1 : (1 : G) ∈ e.source := mem_chart_source E 1
  have hc : c ∈ e.target := e.mapsTo h1
  have hu0 : unchart 0 = 1 := by
    dsimp only [unchart]
    rw [zero_add]
    exact e.left_inv h1
  have hleft : ∀ x ∈ e.source, unchart (chart x) = x := by
    intro x hx
    dsimp only [unchart,chart]
    rw [sub_add_cancel]
    exact e.left_inv hx
  have huSmooth : ∀ y : E, y+c ∈ e.target → ContinuousAt unchart y := by
    intro y hy
    exact (e.symm.continuousAt hy).comp (f := fun z : E => z+c) (continuousAt_id.add continuousAt_const)
  have huCont : ContinuousAt unchart (0 : E) := huSmooth 0 (by simpa only [zero_add] using hc)
  have hright : (fun x => chart (unchart x)) =ᶠ[𝓝 (0 : E)] id := by
    have hcont : ContinuousAt (fun x : E => x+c) 0 := continuousAt_id.add continuousAt_const
    have htarget : ∀ᶠ x in 𝓝 (0 : E), x+c ∈ e.target :=
      hcont.preimage_mem_nhds (by simpa only [zero_add] using e.open_target.mem_nhds hc)
    filter_upwards [htarget] with x hx
    dsimp only [chart,unchart,id]
    rw [e.right_inv hx,add_sub_cancel_right]
  obtain ⟨hμ,hl,hr,hassoc⟩ := lie_group_identity_coordinate_multiplication (G := G) (E := E)
  obtain ⟨f,hfc,⟨O,hOo,hO0,hfO⟩,hfinit,R,r,hR,hr0,hflaw⟩ :=
    exists_uniform_local_one_parameter_curves μ hμ hl hr hassoc
  have hf00 : f (0,0) = 0 := (hfinit.self_of_nhds).1
  have hfcAdd : ContinuousAt (fun p : E × ℝ => f p+c) (0,0) := hfc.add continuousAt_const
  have htarget : ∀ᶠ p : E × ℝ in 𝓝 (0,0), f p+c ∈ e.target :=
    hfcAdd.preimage_mem_nhds (by simpa only [hf00,zero_add] using e.open_target.mem_nhds hc)
  obtain ⟨D₀,hD₀sub,hD₀o,hD₀0⟩ := mem_nhds_iff.mp htarget
  let D := D₀ ∩ O
  have hDo : IsOpen D := hD₀o.inter hOo
  have hD0 : ((0 : E),(0 : ℝ)) ∈ D := ⟨hD₀0,hO0⟩
  let γ : E × ℝ → G := fun p => unchart (f p)
  have hγD : ContinuousOn γ D := by
    intro p hp
    exact ((huSmooth (f p) (hD₀sub hp.1)).comp (hfO.continuousAt (hOo.mem_nhds hp.2))).continuousWithinAt
  have hγ00 : γ (0,0) = 1 := by dsimp only [γ]; rw [hf00,hu0]
  have hγT : Filter.Tendsto γ (𝓝 (0,0)) (𝓝 (1 : G)) := by
    simpa only [hγ00] using (hγD.continuousAt (hDo.mem_nhds hD0)).tendsto
  have hv : Filter.Tendsto (fun p : E × (ℝ × ℝ) => p.1) (𝓝 (0,(0,0))) (𝓝 0) := continuousAt_fst
  have hs : Filter.Tendsto (fun p : E × (ℝ × ℝ) => p.2.1) (𝓝 (0,(0,0))) (𝓝 0) := continuousAt_snd.fst
  have ht : Filter.Tendsto (fun p : E × (ℝ × ℝ) => p.2.2) (𝓝 (0,(0,0))) (𝓝 0) := continuousAt_snd.snd
  have hprodT : Filter.Tendsto (fun p : E × (ℝ × ℝ) => γ (p.1,p.2.1)*γ (p.1,p.2.2))
      (𝓝 (0,(0,0))) (𝓝 (1 : G)) := by
    simpa only [one_mul,Function.comp_def] using
      (hγT.comp (hv.prodMk_nhds hs)).mul (hγT.comp (hv.prodMk_nhds ht))
  have hprod : ∀ᶠ p : E × (ℝ × ℝ) in 𝓝 (0,(0,0)), γ (p.1,p.2.1)*γ (p.1,p.2.2) ∈ e.source :=
    hprodT.eventually (e.open_source.mem_nhds h1)
  obtain ⟨δ,hδ,hδprod⟩ := Metric.mem_nhds_iff.mp hprod
  obtain ⟨η,hη,hηinit⟩ := Metric.mem_nhds_iff.mp hfinit
  let R' := min R (min δ η)
  let r' := min r (δ/2)
  have hR' : 0 < R' := lt_min hR (lt_min hδ hη)
  have hr' : 0 < r' := lt_min hr0 (by positivity)
  refine ⟨γ,D,hDo,hD0,hγD,R',r',hR',hr',?_⟩
  intro v hvR
  have hvδ : ‖v‖ < δ := hvR.trans_le ((min_le_right R (min δ η)).trans (min_le_left δ η))
  have hvη : ‖v‖ < η := hvR.trans_le ((min_le_right R (min δ η)).trans (min_le_right δ η))
  obtain ⟨hfv0,hfvD⟩ := hηinit (show v ∈ Metric.ball 0 η from by simpa only [Metric.mem_ball,dist_zero_right] using hvη)
  have hγv0 : γ (v,0) = 1 := by dsimp only [γ]; rw [hfv0,hu0]
  have hγvc : ContinuousAt (fun t => γ (v,t)) 0 := by
    have hu : ContinuousAt unchart (f (v,0)) := by simpa only [hfv0] using huCont
    exact hu.comp (f := fun t : ℝ => f (v,t)) hfvD.continuousAt
  have hfT : Filter.Tendsto (fun t => f (v,t)) (𝓝 0) (𝓝 0) := by simpa only [hfv0] using hfvD.continuousAt.tendsto
  have hγvD : HasDerivAt (fun t => chart (γ (v,t))) v 0 :=
    hfvD.congr_of_eventuallyEq (hfT.eventually hright)
  apply local_lie_curve_eq_exponential (fun t => γ (v,t)) hγv0 hγvc hγvD hr'
  intro s t hst
  have hsδ : |s| < δ := by have := min_le_right r (δ/2); linarith [abs_nonneg t]
  have htδ : |t| < δ := by have := min_le_right r (δ/2); linarith [abs_nonneg s]
  have hstSource : γ (v,s)*γ (v,t) ∈ e.source := hδprod (show (v,(s,t)) ∈ Metric.ball (0,(0,0)) δ from by
    simpa only [Metric.mem_ball,Prod.dist_eq,dist_zero_right,Real.norm_eq_abs] using max_lt hvδ (max_lt hsδ htδ))
  change unchart (f (v,s+t)) = γ (v,s)*γ (v,t)
  rw [hflaw v (hvR.trans_le (min_le_left _ _)) s t (hst.trans (min_le_left _ _))]
  exact hleft _ hstSource
end DirectedCycles
