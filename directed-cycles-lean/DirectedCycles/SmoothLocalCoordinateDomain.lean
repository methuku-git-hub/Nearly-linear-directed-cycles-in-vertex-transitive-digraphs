import DirectedCycles.LocalSmoothMultiplicationFunction
import DirectedCycles.SmoothLocalIdentityCoordinates

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G]

/-- An actual smooth coordinate law is smooth on an explicit open domain.
The domain records both input charts, the genuine product domain and the
output chart. All its asserted products are actual local products. -/
theorem smooth_local_coordinate_domain (L : LocalGroupAlgebra G)
    (hL : LocalGroupSmoothness (E := E) L) (a : OpenPartialHomeomorph E G)
    (ha0 : (0 : E) ∈ a.source) (ha1 : a 0 = L.one)
    (ha : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a a.source)
    (hai : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a.symm a.target) :
    ∃ (μ : E × E → E) (S : Set (E × E)), IsOpen S ∧ (0,0) ∈ S ∧
      μ (0,0) = 0 ∧ ContDiffOn ℝ ∞ μ S ∧
      (∀ p ∈ S, L.mulRel (a p.1) (a p.2) (a (μ p))) ∧
      (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id ∧
      (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id ∧
      ∀ᶠ p : E × E in 𝓝 (0,0),
        (fun z => μ (μ (p.1,p.2),z)) =ᶠ[𝓝 (0 : E)] (fun z => μ (p.1,μ (p.2,z))) := by
  let pair : E × E → G × G := fun p => (a p.1,a p.2)
  let m : E × E → G := fun p => L.multiplicationFunction (pair p)
  let μ : E × E → E := fun p => a.symm (m p)
  let S : Set (E × E) := {p | p.1 ∈ a.source ∧ p.2 ∈ a.source ∧
    L.Defined (a p.1) (a p.2) ∧ m p ∈ a.target}
  have hpSmooth : ∀ p ∈ S,
      ContMDiffAt 𝓘(ℝ,E × E) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞ pair p := by
    intro p hp
    exact ((ha.contMDiffAt (a.open_source.mem_nhds hp.1)).comp p contDiffAt_fst.contMDiffAt).prodMk
      ((ha.contMDiffAt (a.open_source.mem_nhds hp.2.1)).comp p contDiffAt_snd.contMDiffAt)
  have hmSmooth : ∀ p ∈ S, ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞ m p := by
    intro p hp
    exact (L.multiplicationFunction_contMDiffAt hL hp.2.2.1).comp p (hpSmooth p hp)
  have hμSmooth : ∀ p ∈ S, ContDiffAt ℝ ∞ μ p := by
    intro p hp
    exact ((hai.contMDiffAt (a.open_target.mem_nhds hp.2.2.2)).comp p (hmSmooth p hp)).contDiffAt
  have hSo : IsOpen S := by
    apply isOpen_iff_mem_nhds.2
    intro p hp
    have h₁ := (continuousAt_fst : ContinuousAt (Prod.fst : E × E → E) p).preimage_mem_nhds (a.open_source.mem_nhds hp.1)
    have h₂ := (continuousAt_snd : ContinuousAt (Prod.snd : E × E → E) p).preimage_mem_nhds (a.open_source.mem_nhds hp.2.1)
    have h₃ := (hpSmooth p hp).continuousAt.preimage_mem_nhds (hL.isOpen_domain.mem_nhds hp.2.2.1)
    have h₄ := (hmSmooth p hp).continuousAt.preimage_mem_nhds (a.open_target.mem_nhds hp.2.2.2)
    filter_upwards [h₁,h₂,h₃,h₄] with q hq₁ hq₂ hq₃ hq₄
    exact ⟨hq₁,hq₂,hq₃,hq₄⟩
  have hm0 : m (0,0) = L.one := by
    change L.multiplicationFunction (a 0,a 0) = L.one
    rw [ha1]
    exact L.multiplicationFunction_eq (L.one_mul L.one)
  have hS0 : (0,0) ∈ S := by
    refine ⟨ha0,ha0,?_,?_⟩
    · rw [ha1]; exact ⟨L.one,L.one_mul L.one⟩
    · rw [hm0,← ha1]; exact a.mapsTo ha0
  have hμ0 : μ (0,0) = 0 := by
    change a.symm (m (0,0)) = 0
    rw [hm0,← ha1]
    exact a.left_inv ha0
  have hrel : ∀ p ∈ S, L.mulRel (a p.1) (a p.2) (a (μ p)) := by
    intro p hp
    change L.mulRel (a p.1) (a p.2) (a (a.symm (m p)))
    rw [a.right_inv hp.2.2.2]
    exact L.multiplicationFunction_spec hp.2.2.1
  have hrelNear : ∀ᶠ p : E × E in 𝓝 (0,0), L.mulRel (a p.1) (a p.2) (a (μ p)) := by
    filter_upwards [hSo.mem_nhds hS0] with p hp
    exact hrel p hp
  refine ⟨μ,S,hSo,hS0,hμ0,fun p hp => (hμSmooth p hp).contDiffWithinAt,hrel,?_⟩
  exact local_coordinate_multiplication_laws L a ha0 ha1 μ hμ0 (hμSmooth (0,0) hS0).continuousAt hrelNear
end DirectedCycles
