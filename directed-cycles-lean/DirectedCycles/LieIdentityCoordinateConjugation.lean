module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Tactic
public import DirectedCycles.SmoothAxisNormBound

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
open IsManifold
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- Actual conjugation in identity coordinates is smooth, vanishes on the
first axis and agrees with the identity on the second axis near zero. -/
theorem lie_group_identity_coordinate_conjugation :
    let e := chartAt E (1 : G)
    let c : E := e 1
    let χ : E × E → E := fun p => e (e.symm (p.1+c)*e.symm (p.2+c)*(e.symm (p.1+c))⁻¹)-c
    ContDiffAt ℝ ∞ χ (0,0) ∧
      (∀ᶠ x : E in 𝓝 0, χ (x,0) = 0) ∧
      (fun y => χ (0,y)) =ᶠ[𝓝 (0 : E)] id := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ,E)) (n := ∞)
  let e := chartAt E (1 : G)
  let c : E := e 1
  let chart : G → E := fun x => e x-c
  let unchart : E → G := fun y => e.symm (y+c)
  have h1 : (1 : G) ∈ e.source := mem_chart_source E 1
  have hc : c ∈ e.target := e.mapsTo h1
  have hc1 : chart 1 = 0 := sub_self _
  have hu0 : unchart 0 = 1 := by
    dsimp only [unchart]
    rw [zero_add]
    exact e.left_inv h1
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
  let χ : E × E → E := fun p => chart (unchart p.1*unchart p.2*(unchart p.1)⁻¹)
  have hconj : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞
      (fun p : E × E => unchart p.1*unchart p.2*(unchart p.1)⁻¹) (0,0) :=
    ((hunchartSmooth.comp (0,0) contDiffAt_fst.contMDiffAt).mul
      (hunchartSmooth.comp (0,0) contDiffAt_snd.contMDiffAt)).mul
      (hunchartSmooth.comp (0,0) contDiffAt_fst.contMDiffAt).inv
  have hcSmooth : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞ χ (0,0) := by
    have hchart' : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ chart (unchart 0*unchart 0*(unchart 0)⁻¹) := by
      simpa only [hu0,one_mul,inv_one] using hchartSmooth
    exact hchart'.comp (0,0) hconj
  change ContDiffAt ℝ ∞ χ (0,0) ∧ (∀ᶠ x : E in 𝓝 0, χ (x,0) = 0) ∧
    (fun y => χ (0,y)) =ᶠ[𝓝 (0 : E)] id
  refine ⟨hcSmooth.contDiffAt,?_,?_⟩
  · exact Filter.Eventually.of_forall fun x => by
      simp only [χ,hu0,mul_one,mul_inv_cancel,hc1]
  · simpa only [χ,hu0,one_mul,inv_one,mul_one] using hright

include hLie in
/-- Nearby conjugation has a uniform linear bound in the conjugated
coordinate. The bound is derived from the actual smooth group operations. -/
theorem lie_identity_conjugation_norm_bound :
    let e := chartAt E (1 : G)
    let c : E := e 1
    ∃ r : ℝ, 0 < r ∧ ∀ x y : E, ‖x‖ < r → ‖y‖ < r →
      ‖e (e.symm (x+c)*e.symm (y+c)*(e.symm (x+c))⁻¹)-c‖ ≤ 2*‖y‖ := by
  obtain ⟨hχ,hl,hr⟩ := lie_group_identity_coordinate_conjugation (G := G) (E := E)
  exact smooth_axis_norm_bound _ (hχ.of_le (by norm_num)) hl hr
end DirectedCycles
