import DirectedCycles.LocalMultiplicativeCurveSmooth
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false
open scoped Topology Manifold ContDiff
open IsManifold
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- A continuous one-parameter homomorphism into a smooth Banach Lie group is
smooth in the actual identity coordinates. -/
theorem lieGroup_one_parameter_coordinate_smooth
    (φ : ℝ → G) (hφ0 : φ 0 = 1) (hφcont : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) :
    ContDiffAt ℝ ∞ (fun t => (chartAt E (1 : G)) (φ t)-(chartAt E (1 : G)) 1) 0 := by
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
  let f : ℝ → E := fun t => chart (φ t)
  have hf0 : f 0 = 0 := by dsimp only [f]; rw [hφ0,hc1]
  have hfcont : ContinuousAt f 0 := by
    have hh : ContinuousAt chart (φ 0) := by simpa only [hφ0] using hchart
    exact hh.comp hφcont
  have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), φ t ∈ e.source :=
    hφcont.preimage_mem_nhds (by simpa only [hφ0] using e.open_source.mem_nhds h1)
  obtain ⟨δ,hδ,hδφ⟩ := Metric.mem_nhds_iff.mp hnear
  have hr₀ : 0 < δ/2 := by positivity
  have hcontrol : ∀ t : ℝ, |t| ≤ δ/2 → φ t ∈ e.source := by
    intro t ht
    apply hδφ
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using (show |t|<δ by linarith)
  have hmul : ∀ s t : ℝ, |s|+|t| ≤ δ/2 → f (s+t) = μ (f s,f t) := by
    intro s t hst
    have hs : |s| ≤ δ/2 := by linarith [abs_nonneg t]
    have ht : |t| ≤ δ/2 := by linarith [abs_nonneg s]
    dsimp only [f,μ]
    rw [hleft (φ s) (hcontrol s hs),hleft (φ t) (hcontrol t ht),hφadd]
  exact local_multiplicative_curve_contDiffAt μ hμ hl hr f hf0 hfcont hr₀ hmul

include hLie in
/-- Automatic smoothness at the identity for a continuous real one-parameter
homomorphism, proved from local multiplication coordinates. -/
theorem lieGroup_one_parameter_contMDiffAt_zero
    (φ : ℝ → G) (hφ0 : φ 0 = 1) (hφcont : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) :
    ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ φ 0 := by
  have hv := lieGroup_one_parameter_coordinate_smooth (E := E) φ hφ0 hφcont hφadd
  let e := chartAt E (1 : G)
  have h1 : (1 : G) ∈ e.source := mem_chart_source E 1
  have hc : e 1 ∈ e.target := e.mapsTo h1
  have he : e ∈ maximalAtlas 𝓘(ℝ,E) ∞ G := chart_mem_maximalAtlas (1 : G)
  have hInv : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm (e 1) :=
    contMDiffAt_symm_of_mem_maximalAtlas he hc
  have hcoord : ContDiffAt ℝ ∞ (fun t => e (φ t)) 0 := by
    simpa only [e,sub_add_cancel] using hv.add (contDiffAt_const (c := e 1))
  have hh := hInv.comp_of_eq hcoord.contMDiffAt (show e (φ 0) = e 1 by rw [hφ0])
  apply hh.congr_of_eventuallyEq
  have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), φ t ∈ e.source :=
    hφcont.preimage_mem_nhds (by simpa only [hφ0] using e.open_source.mem_nhds h1)
  filter_upwards [hnear] with t ht
  exact (e.left_inv ht).symm

include hLie in
/-- Every continuous real one-parameter homomorphism into a smooth Banach Lie
group is smooth at every parameter. -/
theorem lieGroup_one_parameter_contMDiff
    (φ : ℝ → G) (hφ0 : φ 0 = 1) (hφcont : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) :
    ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ φ := by
  have hzero := lieGroup_one_parameter_contMDiffAt_zero (E := E) φ hφ0 hφcont hφadd
  intro x
  have hshift : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun t : ℝ => t-x) x :=
    (contDiffAt_id.sub contDiffAt_const).contMDiffAt
  have hc := hzero.comp_of_eq hshift (sub_self x)
  have hl : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun g : G => φ x*g) (φ (x-x)) :=
    contMDiffAt_mul_left
  apply (hl.comp x hc).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => by simpa only [Function.comp_apply,add_sub_cancel] using hφadd x (t-x))
end DirectedCycles
