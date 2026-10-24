import DirectedCycles.CompactSubgroupPowerWindow
import DirectedCycles.CompactNSSApproximation

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- Symmetry turns control of nonnegative powers into containment of the
actual cyclic subgroup, so a subgroup-free window detects the identity. -/
theorem cyclic_identity_of_subgroup_free {B : Set G} (hB : SubgroupFreeSet B)
    (hBi : B⁻¹ = B) (x : G) (hx : ∀ n : ℕ, x^n ∈ B) : x = 1 := by
  have hz : (Subgroup.zpowers x : Set G) ⊆ B := by
    intro y hy
    obtain ⟨k,rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    cases k with
    | ofNat n => simpa only [Int.ofNat_eq_natCast,zpow_natCast] using hx n
    | negSucc n =>
        have h := Set.inv_mem_inv.mpr (hx (n+1))
        simpa only [hBi,zpow_negSucc] using h
  have he := hB (Subgroup.zpowers x) hz
  exact Subgroup.mem_bot.mp (he ▸ Subgroup.mem_zpowers x)

variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- An actual compact-kernel NSS quotient gives an ambient symmetric
precompact window around its kernel whose fourth-power closure detects
cyclic identity in that quotient. -/
theorem compact_kernel_cyclic_window (H : Subgroup G) (hH : IsCompact (H : Set G))
    (N : Subgroup H) [N.Normal] (hN : IsCompact (N : Set H))
    (hnss : HasNoSmallSubgroups (H ⧸ N)) {U : Set G} (hU : IsOpen U)
    (hNU : (N.map H.subtype : Set G) ⊆ U) :
    ∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧ O⁻¹ = O ∧ IsCompact (closure O) ∧
      (N.map H.subtype : Set G) ⊆ O ∧ O ⊆ U ∧
      ∀ x : H, (∀ j : ℕ, (x.val)^j ∈ closure (O^4)) → x ∈ N := by
  obtain ⟨B,hB,hB1,hBfree⟩ := hnss
  let C := B ∩ B⁻¹
  have hC : IsOpen C := hB.inter hB.inv
  have hC1 : (1 : H ⧸ N) ∈ C := ⟨hB1,by simpa using hB1⟩
  have hCi : C⁻¹ = C := by
    ext z
    change (z⁻¹ ∈ B ∧ (z⁻¹)⁻¹ ∈ B) ↔ (z ∈ B ∧ z⁻¹ ∈ B)
    simp only [inv_inv,and_comm]
  let q := QuotientGroup.mk' N
  let R := (H.subtype '' (q ⁻¹' C)ᶜ)ᶜ
  have hR : IsOpen R :=
    (hH.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _
      (hC.preimage QuotientGroup.continuous_mk).isClosed_compl).isOpen_compl
  have hNR : (N.map H.subtype : Set G) ⊆ R := by
    rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    have hyx : y = x := Subtype.ext he
    subst y
    apply hy
    change q x ∈ C
    rw [show q x = 1 from (QuotientGroup.eq_one_iff _).2 hx]
    exact hC1
  have hNc : IsCompact (N.map H.subtype : Set G) := hN.image continuous_subtype_val
  obtain ⟨O,hO,hNO,hOi,hOc,hO4⟩ := compact_subgroup_closed_word_window
    (N.map H.subtype) hNc (hU.inter hR) (fun _ hx => ⟨hNU hx,hNR hx⟩) 4
  have hO1 : (1 : G) ∈ O := hNO (N.map H.subtype).one_mem
  have hOU : O ⊆ U := by
    intro z hz
    exact (hO4 (subset_closure ((Set.pow_subset_pow_right hO1 (by omega : 1 ≤ 4))
      (by simpa only [pow_one] using hz)))).1
  refine ⟨O,hO,hO1,hOi,hOc,hNO,hOU,?_⟩
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply cyclic_identity_of_subgroup_free (hBfree.mono Set.inter_subset_left) hCi
  intro j
  have hRj := (hO4 (hx j)).2
  by_contra hn
  apply hRj
  refine ⟨x^j,?_,rfl⟩
  change q (x^j) ∉ C
  have hn' : (q x)^j ∉ C := hn
  simpa only [map_pow] using hn'
end DirectedCycles
