import DirectedCycles.ShrinkingCyclicWordFamily
import DirectedCycles.GleasonYamabeCompactInput

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
universe u

/-- Every locally compact Hausdorff topological group has subgroup
trapping. All compact-group, Haar finite-trapping and compact-limit inputs
are proved; no general structure theorem is assumed. -/
theorem locally_compact_subgroup_trapping (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] : HasSubgroupTrapping G := by
  intro U hU hU1
  have hbot : IsCompact ((⊥ : Subgroup G) : Set G) := by
    simp only [Subgroup.coe_bot]
    exact isCompact_singleton
  obtain ⟨W,hW,hbotW,hWi,hWc,hWU⟩ := compact_subgroup_closed_word_window
    (⊥ : Subgroup G) hbot hU (by simpa using hU1) 1
  have hW1 : (1 : G) ∈ W := hbotW (Subgroup.one_mem _)
  have hWU' : W ⊆ U := subset_closure.trans (by simpa only [pow_one] using hWU)
  obtain ⟨V,hV,hV1,hVU⟩ := cyclic_core_trapping_precompact hW hW1 hWi hWc
  obtain ⟨H,hHU,hHV⟩ := cyclic_core_subgroup_traps (hVU.trans hWU')
  exact ⟨V,hV,hV1,H,hHU,hHV⟩

/-- The formerly open general trapping input is discharged. -/
theorem locally_compact_subgroup_trapping_theorem : LocallyCompactSubgroupTrappingTheorem.{u} := by
  intro G _ _ _ _ _
  exact locally_compact_subgroup_trapping G

/-- After the compact and general trapping constructions, the remaining
Gleason--Yamabe input is the genuine NSS-to-Lie recognition theorem. -/
theorem gleason_yamabe_of_nss_lie
    (hlie : LocallyCompactNSSLieRecognition.{u}) : GleasonYamabeTheorem.{u} :=
  gleason_yamabe_of_trapping_and_nss_lie locally_compact_subgroup_trapping_theorem hlie
end DirectedCycles
