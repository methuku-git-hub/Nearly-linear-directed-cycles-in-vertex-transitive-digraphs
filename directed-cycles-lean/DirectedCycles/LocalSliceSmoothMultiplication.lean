import DirectedCycles.LocalSliceSmoothProjection
import DirectedCycles.LocalSliceSmoothSection
import Mathlib.Geometry.Manifold.Algebra.LieGroup

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles.LocalNormalSet
variable {H E F : Type*} [Group H] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [hLie : LieGroup 𝓘(ℝ,E) ∞ H]
    {P V W : Set H} (hP : LocalNormalSet P V)
    (hW1 : (1 : H) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)
    (a : OpenPartialHomeomorph (ℝ × F) H) (hWo : IsOpen W) (hWa : W ⊆ a.target)
    (hrel : ∀ x ∈ W, ∀ y ∈ W, x*y⁻¹ ∈ P ↔ (a.symm x).2 = (a.symm y).2)

include hLie in
/-- At every actually defined quotient pair, genuine representative sections and
the ambient group product give a smooth local multiplication satisfying exactly
the existing quotient relation on a neighbourhood. -/
theorem exists_smooth_local_quotient_mul
    (haSmooth : ContMDiffOn 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ a a.source)
    (haInv : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ × F) ∞ a.symm a.target)
    (q r : hP.WindowQuotient hW1 hWi hW6) (hqr : (hP.quotientAlgebra hW1 hWi hW6).Defined q r) :
    letI := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
    ∃ m : hP.WindowQuotient hW1 hWi hW6 × hP.WindowQuotient hW1 hWi hW6 → hP.WindowQuotient hW1 hWi hW6,
      ContMDiffAt (𝓘(ℝ,F).prod 𝓘(ℝ,F)) 𝓘(ℝ,F) ∞ m (q,r) ∧
      ∀ᶠ p in 𝓝 (q,r), (hP.quotientAlgebra hW1 hWi hW6).mulRel p.1 p.2 (m p) := by
  let := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
  obtain ⟨z,x,y,c,hx,hy,_,hxy⟩ := hqr
  subst q
  subst r
  obtain ⟨σ,hσ,hσS,hσret⟩ := hP.exists_smooth_local_slice_section hW1 hWi hW6 a hWo hWa hrel haSmooth x
  obtain ⟨τ,hτ,hτS,hτret⟩ := hP.exists_smooth_local_slice_section hW1 hWi hW6 a hWo hWa hrel haSmooth y
  let Q := hP.WindowQuotient hW1 hWi hW6
  let q₀ := hP.windowMk hW1 hWi hW6 x
  let r₀ := hP.windowMk hW1 hWi hW6 y
  let f : Q × Q → H := fun p => σ p.1*τ p.2
  let π := hP.sliceProjection hW1 hWi hW6 a hWo hWa hrel
  have hfS : ContMDiffAt (𝓘(ℝ,F).prod 𝓘(ℝ,F)) 𝓘(ℝ,E) ∞ f (q₀,r₀) :=
    (hσS.comp (q₀,r₀) contMDiffAt_fst).mul (hτS.comp (q₀,r₀) contMDiffAt_snd)
  have hf0 : f (q₀,r₀) = c.val := by dsimp only [f,q₀,r₀]; rw [hσ,hτ,hxy]
  have hπS := hP.contMDiffAt_sliceProjection hW1 hWi hW6 a hWo hWa hrel haInv c
  have hm : ContMDiffAt (𝓘(ℝ,F).prod 𝓘(ℝ,F)) 𝓘(ℝ,F) ∞ (fun p => π (f p)) (q₀,r₀) :=
    hπS.comp_of_eq hfS hf0
  have hfW : ∀ᶠ p in 𝓝 (q₀,r₀), f p ∈ W :=
    hfS.continuousAt.preimage_mem_nhds (by rw [hf0]; exact hWo.mem_nhds c.property)
  have hret₁ := (continuousAt_fst : ContinuousAt (Prod.fst : Q × Q → Q) (q₀,r₀)).tendsto.eventually hσret
  have hret₂ := (continuousAt_snd : ContinuousAt (Prod.snd : Q × Q → Q) (q₀,r₀)).tendsto.eventually hτret
  refine ⟨fun p => π (f p),hm,?_⟩
  filter_upwards [hret₁,hret₂,hfW] with p hpx hpy hpW
  obtain ⟨hσW,hσq⟩ := hpx
  obtain ⟨hτW,hτq⟩ := hpy
  refine ⟨⟨σ p.1,hσW⟩,⟨τ p.2,hτW⟩,⟨f p,hpW⟩,hσq,hτq,?_,rfl⟩
  exact (hP.sliceProjection_window hW1 hWi hW6 a hWo hWa hrel ⟨f p,hpW⟩).symm
end DirectedCycles.LocalNormalSet
