import DirectedCycles.CompactSubgroupTrapping
import DirectedCycles.CompactKernelAmbientWindow
import DirectedCycles.TrappedSubgroupsInKernel
import DirectedCycles.SubgroupTrappingNormalizer

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
universe u

/-- The compact-kernel NSS output of the topological trapping argument. -/
structure CompactNSSSubquotientData (G : Type u) [Group G] [TopologicalSpace G] (U : Set G) where
  source : Subgroup G
  source_open : IsOpen (source : Set G)
  kernel : Subgroup source
  normal : kernel.Normal
  compact_kernel : IsCompact (kernel : Set source)
  kernel_small : (kernel : Set source) ⊆ source.subtype ⁻¹' U
  nss : let := normal
        HasNoSmallSubgroups (source ⧸ kernel)

/-- Approximation of a specified compact group by actual compact-kernel
NSS quotients. This proposition is not supplied as an axiom. -/
def HasCompactNSSApproximation (H : Type u) [Group H] [TopologicalSpace H] : Prop :=
  ∀ V : Set H, IsOpen V → (1 : H) ∈ V →
    ∃ (N : Subgroup H) (_hN : N.Normal), IsCompact (N : Set H) ∧ (N : Set H) ⊆ V ∧
      HasNoSmallSubgroups (H ⧸ N)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-- The trapping-to-NSS step with a supplied compact subgroup and one
specified NSS quotient of that subgroup. The open normalizer, its actual
compact normal kernel and the NSS quotient are constructed here. -/
theorem nss_subquotient_from_compact_trap (H : Subgroup G) (hH : IsCompact (H : Set G))
    (U V : Set G) (hHU : (H : Set G) ⊆ U) (hV : IsOpen V)
    (htrap : ∀ P : Subgroup G, (P : Set G) ⊆ V → P ≤ H)
    (N : Subgroup H) [N.Normal] (hN : IsCompact (N : Set H))
    (hNV : (N : Set H) ⊆ H.subtype ⁻¹' V) (hnss : HasNoSmallSubgroups (H ⧸ N)) :
    Nonempty (CompactNSSSubquotientData G U) := by
  obtain ⟨B,hB,hB1,hBfree⟩ := hnss
  have hNamb : (N.map H.subtype : Set G) ⊆ V := by
    rintro x ⟨y,hy,rfl⟩
    exact hNV hy
  obtain ⟨W,hW,hW1,hWi,hWV,hWB⟩ := compact_kernel_ambient_window H hH N hN V hV hNamb B hB hB1
  have htrapN := trapped_subgroups_in_kernel H N V (W*(N.map H.subtype : Set G)*W)
    htrap hWV B hBfree hWB
  obtain ⟨hopen,hnss'⟩ := subgroup_trapping_normalizer_quotient_nss (N.map H.subtype) W hW hW1 hWi htrapN
  let A := N.map H.subtype
  let S := Subgroup.normalizer (A : Set G)
  let K := A.subgroupOf S
  have hAc : IsCompact (A : Set G) := hN.image continuous_subtype_val
  have hKc : IsCompact (K : Set S) :=
    (S.isClosed_of_isOpen hopen).isClosedEmbedding_subtypeVal.isCompact_preimage hAc
  refine ⟨{ source := S
            source_open := hopen
            kernel := K
            normal := inferInstance
            compact_kernel := hKc
            kernel_small := ?_
            nss := hnss' }⟩
  intro x hx
  obtain ⟨y,_hy,he⟩ := (show x.val ∈ N.map H.subtype from hx)
  change x.val ∈ U
  rw [← he]
  exact hHU y.property

/-- The complete trapping-to-NSS reduction. The compact approximation
input remains explicit and is not asserted by this conditional theorem. -/
theorem nss_subquotient_of_trapping [LocallyCompactSpace G]
    (htrap : HasSubgroupTrapping G)
    (hcompact : ∀ H : Subgroup G, IsCompact (H : Set G) → HasCompactNSSApproximation H)
    (U : Set G) (hU : IsOpen U) (hU1 : (1 : G) ∈ U) :
    Nonempty (CompactNSSSubquotientData G U) := by
  obtain ⟨V,hV,hV1,H,hH,hHU,hHV⟩ := compact_subgroup_of_trapping htrap U hU hU1
  obtain ⟨N,hNn,hN,hNV,hnss⟩ := hcompact H hH (H.subtype ⁻¹' V)
    (hV.preimage continuous_subtype_val) hV1
  let := hNn
  exact nss_subquotient_from_compact_trap H hH U V hHU hV hHV N hN hNV hnss
end DirectedCycles
