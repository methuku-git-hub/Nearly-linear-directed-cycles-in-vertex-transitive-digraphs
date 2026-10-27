module

public import DirectedCycles.LocalCoordinateMultiplicationLaws
public import DirectedCycles.LocalGroupSmoothness
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
open IsManifold
namespace DirectedCycles
variable {G E : Type*} [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E G]

/-- Every actual smooth identity chart carries a smooth coordinate product
law near the identity, with its genuine relations and identity axes. -/
theorem smooth_local_coordinate_law_at_identity (L : LocalGroupAlgebra G)
    (hL : LocalGroupSmoothness (E := E) L)
    (a : OpenPartialHomeomorph E G) (ha0 : (0 : E) ∈ a.source) (ha1 : a 0 = L.one)
    (haSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a 0)
    (hbSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a.symm L.one) :
    ∃ μ : E × E → E, μ (0,0) = 0 ∧ ContDiffAt ℝ ∞ μ (0,0) ∧
        (∀ᶠ p : E × E in 𝓝 (0,0), L.mulRel (a p.1) (a p.2) (a (μ p))) ∧
        (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id ∧
        (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id ∧
        ∀ᶠ p : E × E in 𝓝 (0,0),
          (fun z => μ (μ (p.1,p.2),z)) =ᶠ[𝓝 (0 : E)] (fun z => μ (p.1,μ (p.2,z))) := by
  obtain ⟨m,hms,hmrel⟩ := hL.smooth_mul L.one L.one ⟨L.one,L.one_mul L.one⟩
  have hm1 : m (L.one,L.one) = L.one := L.unique hmrel.self_of_nhds (L.one_mul _)
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
  exact ⟨μ,hμ0,hμ,hrel,
    local_coordinate_multiplication_laws L a ha0 ha1 μ hμ0 hμ.continuousAt hrel⟩
end DirectedCycles
