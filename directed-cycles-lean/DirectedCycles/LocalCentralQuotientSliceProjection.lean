import DirectedCycles.LocalCentralQuotientSliceChartSmoothness

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles.LocalGroupAlgebra.CentralQuotientData
variable {H E F : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : LocalGroupAlgebra H} {P : Set H} (D : L.CentralQuotientData P)
    (a : OpenPartialHomeomorph (ℝ × F) H) (hWo : IsOpen D.small) (hWa : D.small ⊆ a.target)
    (hrel : ∀ x y : D.small, D.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2)

/-- The actual quotient projection, expressed on the ambient space using the
constructed slice chart. Its asserted projection law is only on the window. -/
noncomputable def sliceProjection : H → D.Carrier :=
  fun x => (D.sliceChart a hWo hWa hrel).symm ((a.symm x).2)

omit [ChartedSpace E H] [NormedSpace ℝ F] in
/-- On the actual window this function is precisely the quotient map. -/
theorem sliceProjection_window (x : D.small) :
    D.sliceProjection a hWo hWa hrel x.val = D.project x := by
  dsimp only [sliceProjection]
  rw [← D.sliceChart_project a hWo hWa hrel x]
  apply OpenPartialHomeomorph.left_inv
  rw [D.sliceChart_source]
  exact Set.mem_univ _

/-- A smooth inverse product chart makes the actual local quotient projection
smooth around every representative in the window. -/
theorem contMDiffAt_sliceProjection
    (haInv : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ × F) ∞ a.symm a.target) (x : D.small) :
    letI := D.sliceChartedSpace a hWo hWa hrel
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ (D.sliceProjection a hWo hWa hrel) x.val := by
  let := D.sliceChartedSpace a hWo hWa hrel
  let b := D.sliceChart a hWo hWa hrel
  have hax := haInv.contMDiffAt (a.open_target.mem_nhds (hWa x.property))
  have hθ : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ (fun y => (a.symm y).2) x.val :=
    contDiffAt_snd.contMDiffAt.comp x.val hax
  have hbq : D.project x ∈ b.source := by
    rw [D.sliceChart_source]
    exact Set.mem_univ _
  have hbt : (a.symm x.val).2 ∈ b.target := by
    rw [← D.sliceChart_project a hWo hWa hrel x]
    exact b.mapsTo hbq
  have hbInv := (D.contMDiffOn_sliceChart_symm a hWo hWa hrel).contMDiffAt
    (b.open_target.mem_nhds hbt)
  exact hbInv.comp x.val hθ
end DirectedCycles.LocalGroupAlgebra.CentralQuotientData
