import DirectedCycles.NSSSubquotientFromTrapping
import DirectedCycles.LieQuotientData
import DirectedCycles.LieGroupNSS

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
universe u

/-- A finite-dimensional real Lie structure on the given topology and
group operations, rather than an unrelated Lie group witness. -/
def HasFiniteDimensionalLieStructure (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∃ d : ℕ, ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin d)) G,
    let := cs
    LieGroup 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ G

/-- The compact structural proposition used in the selected route.
Its unconditional proof is compact_nss_approximation_theorem. -/
def CompactNSSApproximationTheorem : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G], HasCompactNSSApproximation G

/-- The trapping proposition used in the selected route. Its unconditional
proof is locally_compact_subgroup_trapping_theorem. -/
def LocallyCompactSubgroupTrappingTheorem : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G], HasSubgroupTrapping G

/-- The NSS-to-Lie recognition proposition, proved unconditionally in
`GleasonMetricLieStructure` using an actual compatible smooth atlas. -/
def LocallyCompactNSSLieRecognition : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G],
    HasNoSmallSubgroups G → HasFiniteDimensionalLieStructure G

/-- The already constructed Lie NSS neighbourhood gives subgroup NSS. -/
theorem lie_group_has_no_small_subgroups {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) 1 G] : HasNoSmallSubgroups G := by
  obtain ⟨V,hV,hcyclic⟩ := lieGroup_cyclic_nss_neighbourhood (G := G) (E := E)
  obtain ⟨O,hOV,hO,hO1⟩ := mem_nhds_iff.mp hV
  exact ⟨O,hO,hO1,(subgroup_free_of_cyclic_nss hcyclic).mono hOV⟩

/-- Complete assembly of the selected global Gleason--Yamabe route. The
three structural propositions remain explicit inputs to this assembly.
All three inputs are proved in later modules; `gleason_yamabe_theorem`
assembles their unconditional proofs. -/
theorem gleason_yamabe_of_trapping_compact_and_nss_lie
    (htrap : LocallyCompactSubgroupTrappingTheorem.{u})
    (hcompact : CompactNSSApproximationTheorem.{u})
    (hlie : LocallyCompactNSSLieRecognition.{u}) : GleasonYamabeTheorem.{u} := by
  intro G _ _ _ _ _ U hU hU1
  have hc : ∀ H : Subgroup G, IsCompact (H : Set G) → HasCompactNSSApproximation H := by
    intro H hH
    let : CompactSpace H := isCompact_iff_compactSpace.mp hH
    exact hcompact H
  obtain ⟨D⟩ := nss_subquotient_of_trapping (htrap G) hc U hU hU1
  let : D.kernel.Normal := D.normal
  let : IsClosed (D.kernel : Set D.source) := D.compact_kernel.isClosed
  let : LocallyCompactSpace D.source := D.source_open.locallyCompactSpace
  obtain ⟨d,cs,hL⟩ := hlie (D.source ⧸ D.kernel) D.nss
  exact ⟨{ source := D.source
           source_open := D.source_open
           kernel := D.kernel
           normal := D.normal
           compact_kernel := D.compact_kernel
           kernel_small := D.kernel_small
           dimension := d
           charts := cs
           lie := hL }⟩
end DirectedCycles
