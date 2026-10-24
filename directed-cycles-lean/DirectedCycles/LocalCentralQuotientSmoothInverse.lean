import DirectedCycles.LocalCentralQuotientSliceProjection
import DirectedCycles.LocalCentralQuotientSliceSection
import DirectedCycles.LocalGroupSmoothness

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles.LocalGroupAlgebra.CentralQuotientData
variable {H E F : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : LocalGroupAlgebra H} {P : Set H} (D : L.CentralQuotientData P)
    (a : OpenPartialHomeomorph (ℝ × F) H) (hWo : IsOpen D.small) (hWa : D.small ⊆ a.target)
    (hrel : ∀ x y : D.small, D.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2)

/-- Inversion of the actual local central quotient is smooth in the slice
atlas, using the smooth inverse of its local ambient group. -/
theorem contMDiff_algebra_inv (hL : LocalGroupSmoothness (E := E) L)
    (haSmooth : ContMDiffOn 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ a a.source)
    (haInv : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ × F) ∞ a.symm a.target) :
    letI := D.sliceChartedSpace a hWo hWa hrel
    ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ D.algebra.inv := by
  let := D.sliceChartedSpace a hWo hWa hrel
  change ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ D.algebra.inv
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨σ,hσx,hσSmooth,hret⟩ := D.exists_smooth_local_slice_section a hWo hWa hrel haSmooth x
    let π := D.sliceProjection a hWo hWa hrel
    have hxInv : L.inv x.val ∈ D.small := D.inv_mem x.val x.property
    have hπ := D.contMDiffAt_sliceProjection a hWo hWa hrel haInv ⟨L.inv x.val,hxInv⟩
    have hi : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (fun q => L.inv (σ q)) (D.project x) :=
      hL.smooth_inv.contMDiffAt.comp (D.project x) hσSmooth
    have hm : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (fun q => π (L.inv (σ q))) (D.project x) :=
      hπ.comp_of_eq hi (congrArg L.inv hσx)
    apply hm.congr_of_eventuallyEq
    filter_upwards [hret] with q hq
    obtain ⟨hqW,hqeq⟩ := hq
    calc
      D.algebra.inv q = D.algebra.inv (D.project ⟨σ q,hqW⟩) := congrArg D.algebra.inv hqeq.symm
      _ = D.project ⟨L.inv (σ q),D.inv_mem _ hqW⟩ := rfl
      _ = π (L.inv (σ q)) := (D.sliceProjection_window a hWo hWa hrel _).symm
end DirectedCycles.LocalGroupAlgebra.CentralQuotientData
