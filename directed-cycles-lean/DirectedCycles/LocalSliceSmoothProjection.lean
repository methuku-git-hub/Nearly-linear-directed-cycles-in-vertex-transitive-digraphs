import DirectedCycles.LocalSliceChartSmoothness

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

/-- The actual quotient projection, expressed on the ambient space using the
constructed slice chart. Its asserted projection law is only on the window. -/
noncomputable def sliceProjection : H → hP.WindowQuotient hW1 hWi hW6 :=
  fun x => (hP.sliceChart hW1 hWi hW6 a hWo hWa hrel).symm ((a.symm x).2)

omit [ChartedSpace E H] [NormedSpace ℝ F] in
/-- On the actual window this function is precisely the quotient map. -/
theorem sliceProjection_window (x : W) :
    hP.sliceProjection hW1 hWi hW6 a hWo hWa hrel x.val = hP.windowMk hW1 hWi hW6 x := by
  dsimp only [sliceProjection]
  rw [← hP.sliceChart_windowMk hW1 hWi hW6 a hWo hWa hrel x]
  apply OpenPartialHomeomorph.left_inv
  rw [hP.sliceChart_source]
  exact Set.mem_univ _

/-- A smooth inverse product chart makes the actual local quotient projection
smooth around every representative in the window. -/
theorem contMDiffAt_sliceProjection
    (haInv : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ × F) ∞ a.symm a.target) (x : W) :
    letI := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ (hP.sliceProjection hW1 hWi hW6 a hWo hWa hrel) x.val := by
  let := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
  let b := hP.sliceChart hW1 hWi hW6 a hWo hWa hrel
  have hax := haInv.contMDiffAt (a.open_target.mem_nhds (hWa x.property))
  have hθ : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ (fun y => (a.symm y).2) x.val :=
    contDiffAt_snd.contMDiffAt.comp x.val hax
  have hbq : hP.windowMk hW1 hWi hW6 x ∈ b.source := by
    rw [hP.sliceChart_source]
    exact Set.mem_univ _
  have hbt : (a.symm x.val).2 ∈ b.target := by
    rw [← hP.sliceChart_windowMk hW1 hWi hW6 a hWo hWa hrel x]
    exact b.mapsTo hbq
  have hbInv := (hP.contMDiffOn_sliceChart_symm hW1 hWi hW6 a hWo hWa hrel).contMDiffAt
    (b.open_target.mem_nhds hbt)
  exact hbInv.comp x.val hθ
end DirectedCycles.LocalNormalSet
