import DirectedCycles.LocalGroupSmoothness
import DirectedCycles.LocalDifferentiableCoordinateNSS
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false
open scoped Topology Manifold ContDiff
open IsManifold
namespace DirectedCycles
variable {G E : Type*} [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E G]
    [IsManifold 𝓘(ℝ,E) ∞ G]

/-- Every smooth local group has a genuine NSS identity neighbourhood. The
proof uses only its actual smooth multiplication near the identity, and also
excludes all complete power sequences in the constructed neighbourhood. -/
theorem smooth_local_group_nss_neighbourhood (L : LocalGroupAlgebra G)
    (hL : LocalGroupSmoothness (E := E) L) :
    ∃ V : Set G, V ∈ 𝓝 L.one ∧ L.IsNSS V ∧
      (∀ x : G, ∀ p : L.PowerSequence x, (∀ n, p.power n ∈ V) → x = L.one) ∧
      (∀ U : Set G, U ∈ 𝓝 L.one → ∃ M : ℕ, 1 ≤ M ∧
        ∀ x : G, (∀ n ≤ M, L.PowerIn V x n) → x ∈ U) := by
  obtain ⟨m,hms,hmrel⟩ := hL.smooth_mul L.one L.one ⟨L.one,L.one_mul L.one⟩
  have hmSelf : L.mulRel L.one L.one (m (L.one,L.one)) := hmrel.self_of_nhds
  have hm1 : m (L.one,L.one) = L.one := L.unique hmSelf (L.one_mul _)
  let e := chartAt E L.one
  let c : E := e L.one
  let chart : G → E := fun x => e x-c
  let unchart : E → G := fun y => e.symm (y+c)
  have h1 : L.one ∈ e.source := mem_chart_source E L.one
  have hc : c ∈ e.target := e.mapsTo h1
  have hV : e.source ∈ 𝓝 L.one := e.open_source.mem_nhds h1
  have hchart : ContinuousAt chart L.one := (e.continuousAt h1).sub continuousAt_const
  have hc1 : chart L.one = 0 := sub_self _
  have hu0 : unchart 0 = L.one := by
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
  have he : e ∈ maximalAtlas 𝓘(ℝ,E) ∞ G := chart_mem_maximalAtlas L.one
  have heSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e L.one :=
    contMDiffAt_of_mem_maximalAtlas he h1
  have heInvSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm c :=
    contMDiffAt_symm_of_mem_maximalAtlas he hc
  have hchartSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ chart L.one :=
    heSmooth.sub contMDiffAt_const
  have hunchartSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ unchart (0 : E) := by
    have heInvSmooth' : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm ((0 : E)+c) := by
      simpa only [zero_add] using heInvSmooth
    exact heInvSmooth'.comp 0 (contMDiffAt_id.add contMDiffAt_const)
  have hp : ContMDiffAt 𝓘(ℝ,E × E) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun p : E × E => (unchart p.1,unchart p.2)) (0,0) :=
    (hunchartSmooth.comp (0,0) contDiffAt_fst.contMDiffAt).prodMk
      (hunchartSmooth.comp (0,0) contDiffAt_snd.contMDiffAt)
  have hprod : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞
      (fun p : E × E => m (unchart p.1,unchart p.2)) (0,0) :=
    hms.comp_of_eq hp (by simp only [hu0])
  have hcoord : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞
      (fun p : E × E => chart (m (unchart p.1,unchart p.2))) (0,0) :=
    hchartSmooth.comp_of_eq hprod (by simp only [hu0,hm1])
  exact local_nss_neighbourhood_of_differentiable_coordinates L chart unchart e.source hV
    hchart hunchartSmooth.continuousAt hc1 hu0 hleft hright m hmrel
    (hcoord.contDiffAt.differentiableAt (by norm_num))
end DirectedCycles
