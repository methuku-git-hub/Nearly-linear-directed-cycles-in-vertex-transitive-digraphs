import DirectedCycles.SmoothLocalIdentityCoordinates

set_option autoImplicit false
open scoped Topology Manifold ContDiff
open IsManifold
namespace DirectedCycles
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] [IsManifold 𝓘(ℝ,E) ∞ G]

/-- Identity-centred coordinates are smooth on their entire source and target.
This explicit atlas construction avoids inferring a uniform smooth
neighbourhood from infinite differentiability merely at one point. -/
theorem smooth_identity_chart (e₀ : G) :
    ∃ a : OpenPartialHomeomorph E G, (0 : E) ∈ a.source ∧ a 0 = e₀ ∧
      ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a a.source ∧
      ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a.symm a.target := by
  let e := chartAt E e₀
  let c : E := e e₀
  let a := (Homeomorph.addRight c).transOpenPartialHomeomorph e.symm
  have h1 : e₀ ∈ e.source := mem_chart_source E e₀
  have hc : c ∈ e.target := e.mapsTo h1
  have ha0 : (0 : E) ∈ a.source := by
    change (0 : E)+c ∈ e.target
    simpa only [zero_add] using hc
  have ha1 : a 0 = e₀ := by
    change e.symm (0+c) = e₀
    rw [zero_add]
    exact e.left_inv h1
  have he : e ∈ maximalAtlas 𝓘(ℝ,E) ∞ G := chart_mem_maximalAtlas e₀
  refine ⟨a,ha0,ha1,?_,?_⟩
  · intro x hx
    change x+c ∈ e.target at hx
    have hInv := contMDiffAt_symm_of_mem_maximalAtlas he hx
    change ContMDiffWithinAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x : E => e.symm (x+c)) a.source x
    exact (hInv.comp (f := fun x : E => x+c) x (contMDiffAt_id.add contMDiffAt_const)).contMDiffWithinAt
  · intro x hx
    change x ∈ e.source at hx
    have hAt := contMDiffAt_of_mem_maximalAtlas he hx
    change ContMDiffWithinAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x : G => e x + -c) a.target x
    exact (hAt.add contMDiffAt_const).contMDiffWithinAt
end DirectedCycles
