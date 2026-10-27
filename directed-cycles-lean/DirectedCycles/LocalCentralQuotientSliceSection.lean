module

public import DirectedCycles.LocalCentralQuotientSliceChartSmoothness

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles.LocalGroupAlgebra.CentralQuotientData
variable {H E F : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : LocalGroupAlgebra H} {P : Set H} (D : L.CentralQuotientData P)
    (a : OpenPartialHomeomorph (ℝ × F) H) (hWo : IsOpen D.small) (hWa : D.small ⊆ a.target)
    (hrel : ∀ x y : D.small, D.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2)

/-- Fixing the longitudinal coordinate through an actual representative gives
a smooth local section of the actual window quotient. The section stays inside
the window on a proved neighbourhood and retracts exactly under the quotient map. -/
theorem exists_smooth_local_slice_section
    (haSmooth : ContMDiffOn 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ a a.source) (x : D.small) :
    letI := D.sliceChartedSpace a hWo hWa hrel
    ∃ σ : D.Carrier → H,
      σ (D.project x) = x.val ∧
      ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ σ (D.project x) ∧
      ∀ᶠ q in 𝓝 (D.project x),
        ∃ hx : σ q ∈ D.small, D.project ⟨σ q,hx⟩ = q := by
  let := D.sliceChartedSpace a hWo hWa hrel
  let b := D.sliceChart a hWo hWa hrel
  let q₀ := D.project x
  let p := a.symm x.val
  let σ : D.Carrier → H := fun q => a (p.1,b q)
  have hbq : b q₀ = p.2 := D.sliceChart_project a hWo hWa hrel x
  have hp : p ∈ a.source := a.symm.mapsTo (hWa x.property)
  have heq : (p.1,b q₀) = p := by rw [hbq]
  have hσx : σ q₀ = x.val := by
    dsimp only [σ]
    rw [heq]
    exact a.right_inv (hWa x.property)
  have hbSmooth := (D.contMDiff_sliceChart a hWo hWa hrel).contMDiffAt (x := q₀)
  have hpair : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,ℝ × F) ∞ (fun q => (p.1,b q)) q₀ :=
    (contDiffAt_const.prodMk contDiffAt_id).contMDiffAt.comp q₀ hbSmooth
  have haAt := haSmooth.contMDiffAt (a.open_source.mem_nhds hp)
  have hσSmooth : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ σ q₀ := haAt.comp_of_eq hpair heq
  have hσW : ∀ᶠ q in 𝓝 q₀, σ q ∈ D.small :=
    hσSmooth.continuousAt.preimage_mem_nhds (by rw [hσx]; exact hWo.mem_nhds x.property)
  have hpairSource : ∀ᶠ q in 𝓝 q₀, (p.1,b q) ∈ a.source :=
    hpair.continuousAt.preimage_mem_nhds (by rw [heq]; exact a.open_source.mem_nhds hp)
  refine ⟨σ,hσx,hσSmooth,?_⟩
  filter_upwards [hσW,hpairSource] with q hqW hqS
  refine ⟨hqW,?_⟩
  apply b.injOn
  · rw [D.sliceChart_source]
    exact Set.mem_univ _
  · rw [D.sliceChart_source]
    exact Set.mem_univ _
  · rw [D.sliceChart_project]
    change (a.symm (a (p.1,b q))).2 = b q
    rw [a.left_inv hqS]
end DirectedCycles.LocalGroupAlgebra.CentralQuotientData
