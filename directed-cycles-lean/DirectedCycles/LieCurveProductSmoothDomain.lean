import DirectedCycles.LocalCurveProductDerivative
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false
open scoped Topology Manifold ContDiff
open IsManifold
namespace DirectedCycles
variable {G E F : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- The genuine group-product map along a smooth curve is smooth on an actual
open coordinate domain, and its derivative at zero is the prescribed splitting. -/
theorem lie_curve_product_smooth_domain (φ : ℝ → G) (hφ0 : φ 0 = 1)
    (hφ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ φ)
    {v : E} (hv : HasDerivAt (fun t => (chartAt E (1 : G)) (φ t)-(chartAt E (1 : G)) 1) v 0)
    (A : (ℝ × F) ≃L[ℝ] E) (hA : ∀ t : ℝ, A (t,0) = t • v) :
    let g : ℝ × F → E := fun p =>
      (chartAt E (1 : G)) (φ p.1*(chartAt E (1 : G)).symm (A (0,p.2)+(chartAt E (1 : G)) 1))-
        (chartAt E (1 : G)) 1
    ∃ S : Set (ℝ × F), IsOpen S ∧ (0 : ℝ × F) ∈ S ∧ ContDiffOn ℝ ∞ g S ∧
      HasFDerivAt g A.toContinuousLinearMap 0 := by
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
  let g : ℝ × F → E := fun p => chart (φ p.1*unchart (A (0,p.2)))
  have hf0 : f 0 = 0 := by dsimp only [f]; rw [hφ0,hc1]
  have hD := local_curve_product_hasFDerivAt μ (hμ.differentiableAt (by simp)) hl hr f hf0 hv A hA
  have hφnear : ∀ᶠ p : ℝ × F in 𝓝 (0 : ℝ × F), φ p.1 ∈ e.source := by
    have hh : ContinuousAt (fun p : ℝ × F => φ p.1) 0 :=
      (hφ.continuous.comp continuous_fst).continuousAt
    exact hh.preimage_mem_nhds (by simpa only [Prod.fst_zero,hφ0] using e.open_source.mem_nhds h1)
  have hgEq : g =ᶠ[𝓝 (0 : ℝ × F)] (fun p => μ (f p.1,A (0,p.2))) := by
    filter_upwards [hφnear] with p hp
    dsimp only [g,μ,f]
    rw [hleft (φ p.1) hp]
  have hgD : HasFDerivAt g A.toContinuousLinearMap 0 := hD.congr_of_eventuallyEq hgEq
  let z : ℝ × F → E := fun p => A (0,p.2)+c
  have hz : ContDiff ℝ ∞ z :=
    (A.contDiff.comp (contDiff_const.prodMk contDiff_snd)).add contDiff_const
  let w : ℝ × F → G := fun p => φ p.1*unchart (A (0,p.2))
  have hw : ∀ p : ℝ × F, z p ∈ e.target → ContMDiffAt 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ w p := by
    intro p hp
    have hInv : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm (z p) :=
      contMDiffAt_symm_of_mem_maximalAtlas he hp
    have hright' := hInv.comp p hz.contDiffAt.contMDiffAt
    have hleft' := (hφ.contMDiffAt).comp p contDiffAt_fst.contMDiffAt
    exact hleft'.mul hright'
  let S : Set (ℝ × F) := {p | z p ∈ e.target} ∩ {p | w p ∈ e.source}
  have hSo : IsOpen S := by
    have hwcont : ContinuousOn w {p | z p ∈ e.target} :=
      fun p hp => (hw p hp).continuousAt.continuousWithinAt
    exact hwcont.isOpen_inter_preimage (e.open_target.preimage hz.continuous) e.open_source
  have hA0 : A (0,0) = 0 := A.map_zero
  have hS0 : (0 : ℝ × F) ∈ S := by
    constructor
    · change z 0 ∈ e.target
      simpa only [z,Prod.snd_zero,hA0,zero_add] using hc
    · change w 0 ∈ e.source
      simpa only [w,Prod.fst_zero,Prod.snd_zero,hφ0,hA0,hu0,one_mul] using h1
  have hgS : ContDiffOn ℝ ∞ g S := by
    intro p hp
    have he' : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e (w p) :=
      contMDiffAt_of_mem_maximalAtlas he hp.2
    have hchart' := he'.sub (contMDiffAt_const (c := c))
    exact (hchart'.comp p (hw p hp.1)).contDiffAt.contDiffWithinAt
  exact ⟨S,hSo,hS0,hgS,hgD⟩
end DirectedCycles
