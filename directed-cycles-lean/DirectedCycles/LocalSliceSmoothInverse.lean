module

public import DirectedCycles.LocalSliceSmoothProjection
public import DirectedCycles.LocalSliceSmoothSection
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

@[expose] public section

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
/-- Actual inversion of the window quotient is smooth in the constructed slice
atlas, by smooth local sections and the actual group inverse. -/
theorem contMDiff_quotientInv_slice
    (haSmooth : ContMDiffOn 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ a a.source)
    (haInv : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ × F) ∞ a.symm a.target) :
    letI := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
    ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (hP.quotientInv hW1 hWi hW6) := by
  let := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
  change ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (hP.quotientInv hW1 hWi hW6)
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨σ,hσx,hσSmooth,hret⟩ := hP.exists_smooth_local_slice_section hW1 hWi hW6 a hWo hWa hrel haSmooth x
    let π := hP.sliceProjection hW1 hWi hW6 a hWo hWa hrel
    have hxInv : x.val⁻¹ ∈ W := window_inv_mem hWi x.property
    have hπ := hP.contMDiffAt_sliceProjection hW1 hWi hW6 a hWo hWa hrel haInv ⟨x.val⁻¹,hxInv⟩
    have hm : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (fun q => π ((σ q)⁻¹)) (hP.windowMk hW1 hWi hW6 x) :=
      hπ.comp_of_eq hσSmooth.inv (congrArg Inv.inv hσx)
    apply hm.congr_of_eventuallyEq
    filter_upwards [hret] with q hq
    obtain ⟨hqW,hqeq⟩ := hq
    calc
      hP.quotientInv hW1 hWi hW6 q = hP.quotientInv hW1 hWi hW6 (hP.windowMk hW1 hWi hW6 ⟨σ q,hqW⟩) :=
        congrArg (hP.quotientInv hW1 hWi hW6) hqeq.symm
      _ = hP.windowMk hW1 hWi hW6 ⟨(σ q)⁻¹,window_inv_mem hWi hqW⟩ := rfl
      _ = π ((σ q)⁻¹) := (hP.sliceProjection_window hW1 hWi hW6 a hWo hWa hrel _).symm
end DirectedCycles.LocalNormalSet
