import DirectedCycles.CompactOpenStabilizer
import DirectedCycles.TotallyDisconnectedNeighbourhoods

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Van Dantzig's compact-open-subgroup theorem, with the subgroup chosen
inside the prescribed identity neighbourhood. -/
theorem exists_compact_open_subgroup {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧ IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  obtain ⟨V,hVc,hVo,hV1,hVU⟩ := exists_compact_open_neighbourhood hU
  obtain ⟨H,hHo,hHc,hHV⟩ := compact_open_subgroup_of_compact_open hVc hVo hV1
  exact ⟨H,hHo,hHc,hHV.trans hVU⟩

/-- In the totally disconnected locally compact case, NSS forces the
identity to be isolated. -/
theorem totallyDisconnected_nss_one_open {U : Set G} (hU : U ∈ 𝓝 (1 : G))
    (hNSS : ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥) :
    IsOpen ({1} : Set G) := by
  obtain ⟨H,hHo,_,hHU⟩ := exists_compact_open_subgroup hU
  have he := hNSS H hHU
  simpa only [he,Subgroup.coe_bot] using hHo
end DirectedCycles

namespace DirectedCycles
open scoped Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- A locally compact Hausdorff totally disconnected NSS group is discrete. -/
theorem totallyDisconnected_nss_discrete {U : Set G} (hU : U ∈ 𝓝 (1 : G))
    (hNSS : ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥) : DiscreteTopology G :=
  discreteTopology_of_isOpen_singleton_one (totallyDisconnected_nss_one_open hU hNSS)
end DirectedCycles
