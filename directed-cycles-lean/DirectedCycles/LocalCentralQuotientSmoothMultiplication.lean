import DirectedCycles.LocalCentralQuotientSliceProjection
import DirectedCycles.LocalCentralQuotientSliceSection
import DirectedCycles.LocalSmoothMultiplicationFunction

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles.LocalGroupAlgebra.CentralQuotientData
variable {H E F : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : LocalGroupAlgebra H} {P : Set H} (D : L.CentralQuotientData P)
    (a : OpenPartialHomeomorph (ℝ × F) H) (hWo : IsOpen D.small) (hWa : D.small ⊆ a.target)
    (hrel : ∀ x y : D.small, D.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2)

/-- Every defined quotient pair has an actual smooth multiplication germ,
constructed from representative sections and the local ambient product. -/
theorem exists_smooth_algebra_mul (hL : LocalGroupSmoothness (E := E) L)
    (haSmooth : ContMDiffOn 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ a a.source)
    (haInv : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ × F) ∞ a.symm a.target)
    (q r : D.Carrier) (hqr : D.algebra.Defined q r) :
    letI := D.sliceChartedSpace a hWo hWa hrel
    ∃ m : D.Carrier × D.Carrier → D.Carrier,
      ContMDiffAt (𝓘(ℝ,F).prod 𝓘(ℝ,F)) 𝓘(ℝ,F) ∞ m (q,r) ∧
      ∀ᶠ p in 𝓝 (q,r), D.algebra.mulRel p.1 p.2 (m p) := by
  let := D.sliceChartedSpace a hWo hWa hrel
  obtain ⟨z,x,y,c,hx,hy,_,hxy⟩ := hqr
  subst q
  subst r
  obtain ⟨σ,hσ,hσS,hσret⟩ := D.exists_smooth_local_slice_section a hWo hWa hrel haSmooth x
  obtain ⟨τ,hτ,hτS,hτret⟩ := D.exists_smooth_local_slice_section a hWo hWa hrel haSmooth y
  let q₀ := D.project x
  let r₀ := D.project y
  let pair : D.Carrier × D.Carrier → H × H := fun p => (σ p.1,τ p.2)
  let f : D.Carrier × D.Carrier → H := fun p => L.multiplicationFunction (pair p)
  let π := D.sliceProjection a hWo hWa hrel
  have hpS : ContMDiffAt (𝓘(ℝ,F).prod 𝓘(ℝ,F)) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞ pair (q₀,r₀) :=
    (hσS.comp (q₀,r₀) contMDiffAt_fst).prodMk (hτS.comp (q₀,r₀) contMDiffAt_snd)
  have hp0 : pair (q₀,r₀) = (x.val,y.val) := by dsimp only [pair,q₀,r₀]; rw [hσ,hτ]
  have hfS : ContMDiffAt (𝓘(ℝ,F).prod 𝓘(ℝ,F)) 𝓘(ℝ,E) ∞ f (q₀,r₀) :=
    (L.multiplicationFunction_contMDiffAt hL ⟨c.val,hxy⟩).comp_of_eq hpS hp0
  have hf0 : f (q₀,r₀) = c.val := by
    dsimp only [f]
    rw [hp0]
    exact L.multiplicationFunction_eq hxy
  have hm : ContMDiffAt (𝓘(ℝ,F).prod 𝓘(ℝ,F)) 𝓘(ℝ,F) ∞ (fun p => π (f p)) (q₀,r₀) :=
    (D.contMDiffAt_sliceProjection a hWo hWa hrel haInv c).comp_of_eq hfS hf0
  have hfW : ∀ᶠ p in 𝓝 (q₀,r₀), f p ∈ D.small :=
    hfS.continuousAt.preimage_mem_nhds (by rw [hf0]; exact hWo.mem_nhds c.property)
  have hpDom : ∀ᶠ p in 𝓝 (q₀,r₀), L.Defined (σ p.1) (τ p.2) := by
    have hh := hpS.continuousAt.preimage_mem_nhds
      (hL.isOpen_domain.mem_nhds (show L.Defined (pair (q₀,r₀)).1 (pair (q₀,r₀)).2 from by rw [hp0]; exact ⟨c.val,hxy⟩))
    exact hh
  have hret₁ := (continuousAt_fst : ContinuousAt (Prod.fst : D.Carrier × D.Carrier → D.Carrier) (q₀,r₀)).tendsto.eventually hσret
  have hret₂ := (continuousAt_snd : ContinuousAt (Prod.snd : D.Carrier × D.Carrier → D.Carrier) (q₀,r₀)).tendsto.eventually hτret
  refine ⟨fun p => π (f p),hm,?_⟩
  filter_upwards [hret₁,hret₂,hfW,hpDom] with p hpx hpy hpW hpD
  obtain ⟨hσW,hσq⟩ := hpx
  obtain ⟨hτW,hτq⟩ := hpy
  exact ⟨⟨σ p.1,hσW⟩,⟨τ p.2,hτW⟩,⟨f p,hpW⟩,hσq,hτq,
    (D.sliceProjection_window a hWo hWa hrel ⟨f p,hpW⟩).symm,L.multiplicationFunction_spec hpD⟩
end DirectedCycles.LocalGroupAlgebra.CentralQuotientData
