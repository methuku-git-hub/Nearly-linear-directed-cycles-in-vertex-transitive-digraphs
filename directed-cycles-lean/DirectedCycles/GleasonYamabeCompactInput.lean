import DirectedCycles.CompactNSSApproximation
import DirectedCycles.GleasonYamabeReduction

set_option autoImplicit false
namespace DirectedCycles
universe u

/-- The compact structural input is now proved from Haar measure and
the spectral theorem; this is not a new assumed classification theorem. -/
theorem compact_nss_approximation_theorem : CompactNSSApproximationTheorem.{u} := by
  intro G _ _ _ _ _
  exact compact_nss_approximation G

/-- The remaining global Gleason--Yamabe inputs after discharging the
compact-group case: local subgroup trapping and locally compact NSS-to-Lie
recognition. These are explicit premises of this reduction; the complete
construction supplies both in the unconditional Gleason--Yamabe theorem. -/
theorem gleason_yamabe_of_trapping_and_nss_lie
    (htrap : LocallyCompactSubgroupTrappingTheorem.{u})
    (hlie : LocallyCompactNSSLieRecognition.{u}) : GleasonYamabeTheorem.{u} :=
  gleason_yamabe_of_trapping_compact_and_nss_lie htrap compact_nss_approximation_theorem hlie

/-- Compact groups satisfy subgroup trapping unconditionally, by pulling
back an NSS neighbourhood from the constructed small-kernel quotient. -/
theorem compact_group_subgroup_trapping (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] : HasSubgroupTrapping G := by
  intro U hU hU1
  obtain ⟨N,hN,_,hNU,V,hV,hV1,hfree⟩ := compact_nss_approximation G U hU hU1
  let := hN
  let q := QuotientGroup.mk' N
  refine ⟨q ⁻¹' V,hV.preimage continuous_quotient_mk',?_,N,hNU,?_⟩
  · simpa only [Set.mem_preimage,map_one] using hV1
  · intro S hS
    have hmap : (S.map q : Set (G ⧸ N)) ⊆ V := by
      rintro y ⟨x,hx,rfl⟩
      exact hS hx
    have he := hfree (S.map q) hmap
    intro x hx
    have hxq : q x ∈ S.map q := Subgroup.mem_map.mpr ⟨x,hx,rfl⟩
    rw [he] at hxq
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hxq)
end DirectedCycles
