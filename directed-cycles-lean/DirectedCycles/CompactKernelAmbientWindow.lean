import DirectedCycles.CompactTwoSidedWindow
import DirectedCycles.SubgroupNSSBasics

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-- Lift a quotient identity neighbourhood to an ambient two-sided compact
kernel window. The ambient open set is obtained using the closed inclusion
of the compact containing subgroup, rather than extending its quotient map. -/
theorem compact_kernel_ambient_window (H : Subgroup G) (hH : IsCompact (H : Set G))
    (N : Subgroup H) [N.Normal] (hN : IsCompact (N : Set H))
    (V : Set G) (hV : IsOpen V) (hNV : (N.map H.subtype : Set G) ⊆ V)
    (B : Set (H ⧸ N)) (hB : IsOpen B) (hB1 : (1 : H ⧸ N) ∈ B) :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧ (∀ x ∈ W, x⁻¹ ∈ W) ∧
      W*(N.map H.subtype : Set G)*W ⊆ V ∧
      ∀ x : H, x.val ∈ W*(N.map H.subtype : Set G)*W → QuotientGroup.mk' N x ∈ B := by
  let q := QuotientGroup.mk' N
  let O := (H.subtype '' (q ⁻¹' B)ᶜ)ᶜ
  have hO : IsOpen O :=
    (hH.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _
      (hB.preimage QuotientGroup.continuous_mk).isClosed_compl).isOpen_compl
  have hNO : (N.map H.subtype : Set G) ⊆ O := by
    rintro n ⟨x,hx,rfl⟩
    rintro ⟨y,hy,he⟩
    have hxy : y = x := Subtype.ext he
    subst y
    apply hy
    change q x ∈ B
    rw [show q x = 1 from (QuotientGroup.eq_one_iff _).2 hx]
    exact hB1
  have hNc : IsCompact (N.map H.subtype : Set G) := hN.image continuous_subtype_val
  obtain ⟨W,hW,hW1,hWi,hWR⟩ := compact_two_sided_window
    (N.map H.subtype : Set G) (V ∩ O) hNc (hV.inter hO) (fun _ hx => ⟨hNV hx,hNO hx⟩)
  refine ⟨W,hW,hW1,hWi,hWR.trans Set.inter_subset_left,?_⟩
  intro x hx
  by_contra hn
  exact (hWR hx).2 ⟨x,hn,rfl⟩
end DirectedCycles
