module

public import DirectedCycles.LocalSliceChartSmoothness

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles.LocalNormalSet
variable {H E F : Type*} [Group H] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P V W : Set H} (hP : LocalNormalSet P V)
    (hW1 : (1 : H) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)
    (a : OpenPartialHomeomorph (ℝ × F) H) (hWo : IsOpen W) (hWa : W ⊆ a.target)
    (hrel : ∀ x ∈ W, ∀ y ∈ W, x*y⁻¹ ∈ P ↔ (a.symm x).2 = (a.symm y).2)

/-- Fixing the longitudinal coordinate through an actual representative gives
a smooth local section of the actual window quotient. The section stays inside
the window on a proved neighbourhood and retracts exactly under the quotient map. -/
theorem exists_smooth_local_slice_section
    (haSmooth : ContMDiffOn 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ a a.source) (x : W) :
    letI := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
    ∃ σ : hP.WindowQuotient hW1 hWi hW6 → H,
      σ (hP.windowMk hW1 hWi hW6 x) = x.val ∧
      ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ σ (hP.windowMk hW1 hWi hW6 x) ∧
      ∀ᶠ q in 𝓝 (hP.windowMk hW1 hWi hW6 x),
        ∃ hx : σ q ∈ W, hP.windowMk hW1 hWi hW6 ⟨σ q,hx⟩ = q := by
  let := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
  let b := hP.sliceChart hW1 hWi hW6 a hWo hWa hrel
  let q₀ := hP.windowMk hW1 hWi hW6 x
  let p := a.symm x.val
  let σ : hP.WindowQuotient hW1 hWi hW6 → H := fun q => a (p.1,b q)
  have hbq : b q₀ = p.2 := hP.sliceChart_windowMk hW1 hWi hW6 a hWo hWa hrel x
  have hp : p ∈ a.source := a.symm.mapsTo (hWa x.property)
  have heq : (p.1,b q₀) = p := by rw [hbq]
  have hσx : σ q₀ = x.val := by
    dsimp only [σ]
    rw [heq]
    exact a.right_inv (hWa x.property)
  have hbSmooth := (hP.contMDiff_sliceChart hW1 hWi hW6 a hWo hWa hrel).contMDiffAt (x := q₀)
  have hpair : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,ℝ × F) ∞ (fun q => (p.1,b q)) q₀ :=
    (contDiffAt_const.prodMk contDiffAt_id).contMDiffAt.comp q₀ hbSmooth
  have haAt := haSmooth.contMDiffAt (a.open_source.mem_nhds hp)
  have hσSmooth : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ σ q₀ := haAt.comp_of_eq hpair heq
  have hσW : ∀ᶠ q in 𝓝 q₀, σ q ∈ W :=
    hσSmooth.continuousAt.preimage_mem_nhds (by rw [hσx]; exact hWo.mem_nhds x.property)
  have hpairSource : ∀ᶠ q in 𝓝 q₀, (p.1,b q) ∈ a.source :=
    hpair.continuousAt.preimage_mem_nhds (by rw [heq]; exact a.open_source.mem_nhds hp)
  refine ⟨σ,hσx,hσSmooth,?_⟩
  filter_upwards [hσW,hpairSource] with q hqW hqS
  refine ⟨hqW,?_⟩
  apply b.injOn
  · rw [hP.sliceChart_source]
    exact Set.mem_univ _
  · rw [hP.sliceChart_source]
    exact Set.mem_univ _
  · rw [hP.sliceChart_windowMk]
    change (a.symm (a (p.1,b q))).2 = b q
    rw [a.left_inv hqS]
end DirectedCycles.LocalNormalSet
