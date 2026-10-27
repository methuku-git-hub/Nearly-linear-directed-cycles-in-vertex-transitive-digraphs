module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
open IsManifold
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- Actual identity-chart multiplication is smooth, has the identity axes and
satisfies local associativity on genuine coordinate neighbourhoods. -/
theorem lie_group_identity_coordinate_multiplication :
    let e := chartAt E (1 : G)
    let c : E := e 1
    let μ : E × E → E := fun p => e (e.symm (p.1+c)*e.symm (p.2+c))-c
    ContDiffAt ℝ ∞ μ (0,0) ∧
      (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id ∧
      (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id ∧
      ∀ᶠ p : E × E in 𝓝 (0,0),
        (fun z => μ (μ (p.1,p.2),z)) =ᶠ[𝓝 (0 : E)] (fun z => μ (p.1,μ (p.2,z))) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ,E)) (n := ∞)
  let e := chartAt E (1 : G)
  let c : E := e 1
  let chart : G → E := fun x => e x-c
  let unchart : E → G := fun y => e.symm (y+c)
  have h1 : (1 : G) ∈ e.source := mem_chart_source E 1
  have hc : c ∈ e.target := e.mapsTo h1
  have hchart : ContinuousAt chart 1 := (e.continuousAt h1).sub continuousAt_const
  have hc1 : chart 1 = 0 := sub_self _
  have hu0 : unchart 0 = 1 := by
    dsimp only [unchart]
    rw [zero_add]
    exact e.left_inv h1
  have hleft : ∀ x ∈ e.source, unchart (chart x) = x := by
    intro x hx
    dsimp only [unchart,chart]
    rw [sub_add_cancel]
    exact e.left_inv hx
  have hright : (fun x => chart (unchart x)) =ᶠ[𝓝 (0 : E)] id := by
    have hcont : ContinuousAt (fun x : E => x+c) 0 := continuousAt_id.add continuousAt_const
    have htarget : ∀ᶠ x in 𝓝 (0 : E), x+c ∈ e.target :=
      hcont.preimage_mem_nhds (by simpa only [zero_add] using e.open_target.mem_nhds hc)
    filter_upwards [htarget] with x hx
    dsimp only [chart,unchart,id]
    rw [e.right_inv hx,add_sub_cancel_right]
  have he : e ∈ maximalAtlas 𝓘(ℝ,E) ∞ G := chart_mem_maximalAtlas (1 : G)
  have heSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e (1 : G) :=
    contMDiffAt_of_mem_maximalAtlas he h1
  have heInvSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm c :=
    contMDiffAt_symm_of_mem_maximalAtlas he hc
  have hchartSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ chart (1 : G) :=
    heSmooth.sub contMDiffAt_const
  have hunchartSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ unchart (0 : E) := by
    have heInvSmooth' : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm ((0 : E)+c) := by
      simpa only [zero_add] using heInvSmooth
    exact heInvSmooth'.comp 0 (contMDiffAt_id.add contMDiffAt_const)
  have hmulSmooth : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞
      (fun p : E × E => unchart p.1*unchart p.2) (0,0) :=
    (hunchartSmooth.comp (0,0) contDiffAt_fst.contMDiffAt).mul (hunchartSmooth.comp (0,0) contDiffAt_snd.contMDiffAt)
  have hm : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞
      (fun p : E × E => chart (unchart p.1*unchart p.2)) (0,0) := by
    have hs : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ chart (unchart 0*unchart 0) := by
      simpa only [hu0,one_mul] using hchartSmooth
    exact hs.comp (0,0) hmulSmooth
  let μ : E × E → E := fun p => chart (unchart p.1*unchart p.2)
  have hμ : ContDiffAt ℝ ∞ μ (0,0) := hm.contDiffAt
  have hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id := by
    simpa only [μ,hu0,mul_one] using hright
  have hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id := by
    simpa only [μ,hu0,one_mul] using hright
  refine ⟨hμ,hl,hr,?_⟩
  have huCont : ContinuousAt unchart (0 : E) := hunchartSmooth.continuousAt
  have huT : Filter.Tendsto unchart (𝓝 (0 : E)) (𝓝 (1 : G)) := by
    simpa only [hu0] using huCont.tendsto
  have hfst : Filter.Tendsto (fun p : E × E => p.1) (𝓝 (0,0)) (𝓝 0) := continuousAt_fst
  have hsnd : Filter.Tendsto (fun p : E × E => p.2) (𝓝 (0,0)) (𝓝 0) := continuousAt_snd
  have hprodT : Filter.Tendsto (fun p : E × E => unchart p.1*unchart p.2) (𝓝 (0,0)) (𝓝 (1 : G)) := by
    simpa only [one_mul,Function.comp_def] using (huT.comp hfst).mul (huT.comp hsnd)
  have hprod : ∀ᶠ p : E × E in 𝓝 (0,0), unchart p.1*unchart p.2 ∈ e.source :=
    hprodT.eventually (e.open_source.mem_nhds h1)
  have hsecond : ∀ᶠ p : E × E in 𝓝 (0,0), unchart p.2 ∈ e.source :=
    (huT.comp hsnd).eventually (e.open_source.mem_nhds h1)
  filter_upwards [hprod,hsecond] with p hp hy
  have hzCont : ContinuousAt (fun z : E => unchart p.2*unchart z) 0 :=
    continuousAt_const.mul huCont
  have hz : ∀ᶠ z : E in 𝓝 0, unchart p.2*unchart z ∈ e.source :=
    hzCont.preimage_mem_nhds (by simpa only [hu0,mul_one] using e.open_source.mem_nhds hy)
  filter_upwards [hz] with z hz
  change chart (unchart (chart (unchart p.1*unchart p.2))*unchart z) =
    chart (unchart p.1*unchart (chart (unchart p.2*unchart z)))
  rw [hleft _ hp,hleft _ hz,mul_assoc]
end DirectedCycles
