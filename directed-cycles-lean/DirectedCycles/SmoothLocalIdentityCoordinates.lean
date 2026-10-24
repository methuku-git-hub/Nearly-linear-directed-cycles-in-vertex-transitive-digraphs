import DirectedCycles.LocalCoordinateMultiplicationLaws
import DirectedCycles.LocalGroupSmoothness
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

/-- A smooth local group supplies actual identity coordinates and a smooth
coordinate law, with genuine local product relations, identity axes and
associativity. No global ambient group or globalization is required. -/
theorem smooth_local_identity_coordinates (L : LocalGroupAlgebra G)
    (hL : LocalGroupSmoothness (E := E) L) :
    ∃ a : OpenPartialHomeomorph E G, (0 : E) ∈ a.source ∧ a 0 = L.one ∧
      ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a 0 ∧
      ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a.symm L.one ∧
      ∃ μ : E × E → E, μ (0,0) = 0 ∧ ContDiffAt ℝ ∞ μ (0,0) ∧
        (∀ᶠ p : E × E in 𝓝 (0,0), L.mulRel (a p.1) (a p.2) (a (μ p))) ∧
        (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id ∧
        (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id ∧
        ∀ᶠ p : E × E in 𝓝 (0,0),
          (fun z => μ (μ (p.1,p.2),z)) =ᶠ[𝓝 (0 : E)] (fun z => μ (p.1,μ (p.2,z))) := by
  obtain ⟨m,hms,hmrel⟩ := hL.smooth_mul L.one L.one ⟨L.one,L.one_mul L.one⟩
  have hm1 : m (L.one,L.one) = L.one := L.unique hmrel.self_of_nhds (L.one_mul _)
  let e := chartAt E L.one
  let c : E := e L.one
  let a := (Homeomorph.addRight c).transOpenPartialHomeomorph e.symm
  have h1 : L.one ∈ e.source := mem_chart_source E L.one
  have hc : c ∈ e.target := e.mapsTo h1
  have ha0 : (0 : E) ∈ a.source := by
    change (0 : E)+c ∈ e.target
    simpa only [zero_add] using hc
  have ha1 : a 0 = L.one := by
    change e.symm (0+c) = L.one
    rw [zero_add]
    exact e.left_inv h1
  have he : e ∈ maximalAtlas 𝓘(ℝ,E) ∞ G := chart_mem_maximalAtlas L.one
  have heSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e L.one :=
    contMDiffAt_of_mem_maximalAtlas he h1
  have heInvSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm c :=
    contMDiffAt_symm_of_mem_maximalAtlas he hc
  have haSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a (0 : E) := by
    have heInvSmooth' : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm ((0 : E)+c) := by
      simpa only [zero_add] using heInvSmooth
    change ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x : E => e.symm (x+c)) 0
    exact heInvSmooth'.comp (f := fun x : E => x+c) 0 (contMDiffAt_id.add contMDiffAt_const)
  have hbSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a.symm L.one := by
    change ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x : G => e x + -c) L.one
    exact heSmooth.add contMDiffAt_const
  have hp : ContMDiffAt 𝓘(ℝ,E × E) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun p : E × E => (a p.1,a p.2)) (0,0) :=
    (haSmooth.comp (0,0) contDiffAt_fst.contMDiffAt).prodMk
      (haSmooth.comp (0,0) contDiffAt_snd.contMDiffAt)
  have hprod : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞
      (fun p : E × E => m (a p.1,a p.2)) (0,0) :=
    hms.comp_of_eq hp (by simp only [ha1])
  let μ : E × E → E := fun p => a.symm (m (a p.1,a p.2))
  have hμ : ContDiffAt ℝ ∞ μ (0,0) :=
    (hbSmooth.comp_of_eq hprod (by simp only [ha1,hm1])).contDiffAt
  have hμ0 : μ (0,0) = 0 := by
    change a.symm (m (a 0,a 0)) = 0
    rw [ha1,hm1,← ha1]
    exact a.left_inv ha0
  have hrel : ∀ᶠ p : E × E in 𝓝 (0,0), L.mulRel (a p.1) (a p.2) (a (μ p)) := by
    have hpT : Filter.Tendsto (fun p : E × E => (a p.1,a p.2)) (𝓝 (0,0)) (𝓝 (L.one,L.one)) := by
      simpa only [ha1] using hp.continuousAt.tendsto
    have hmT : Filter.Tendsto (fun p : E × E => m (a p.1,a p.2)) (𝓝 (0,0)) (𝓝 L.one) := by
      simpa only [ha1,hm1] using hprod.continuousAt.tendsto
    have ht : L.one ∈ a.target := ha1 ▸ a.mapsTo ha0
    filter_upwards [hpT.eventually hmrel,hmT.eventually (a.open_target.mem_nhds ht)] with p hp ht
    dsimp only [μ]
    rw [a.right_inv ht]
    exact hp
  exact ⟨a,ha0,ha1,haSmooth,hbSmooth,μ,hμ0,hμ,hrel,
    local_coordinate_multiplication_laws L a ha0 ha1 μ hμ0 hμ.continuousAt hrel⟩
end DirectedCycles
