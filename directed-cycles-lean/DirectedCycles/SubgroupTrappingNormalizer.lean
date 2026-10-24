import DirectedCycles.SubgroupNSSBasics
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- A sufficiently small two-sided kernel window forces its identity
neighbourhood to normalize the actual kernel. Each conjugate is a genuine
subgroup to which the trapping conclusion applies. -/
theorem subgroup_trapping_window_normalizes (N : Subgroup G) (W : Set G)
    (hWi : ∀ x ∈ W, x⁻¹ ∈ W)
    (htrap : ∀ P : Subgroup G, (P : Set G) ⊆ W*(N : Set G)*W → P ≤ N) :
    W ⊆ (Subgroup.normalizer (N : Set G)) := by
  have hconj : ∀ g ∈ W, ∀ n ∈ N, g*n*g⁻¹ ∈ N := by
    intro g hg n hn
    let P := N.map (MulAut.conj g).toMonoidHom
    have hPW : (P : Set G) ⊆ W*(N : Set G)*W := by
      rintro x ⟨y,hy,rfl⟩
      exact ⟨g*y,⟨g,hg,y,hy,rfl⟩,g⁻¹,hWi g hg,rfl⟩
    exact htrap P hPW (Subgroup.mem_map.mpr ⟨n,hn,rfl⟩)
  intro g hg
  apply Subgroup.mem_normalizer_iff.2
  intro n
  constructor
  · exact hconj g hg n
  · intro hn
    have hh := hconj g⁻¹ (hWi g hg) (g*n*g⁻¹) hn
    simpa only [inv_inv,inv_mul_cancel_left,mul_assoc,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh

/-- The quotient of the actual normalizer has a subgroup-free identity
window. Pullbacks of its small subgroups are trapped inside the same kernel. -/
theorem subgroup_trapping_normalizer_quotient_free (N : Subgroup G) (W : Set G)
    (hW1 : (1 : G) ∈ W)
    (htrap : ∀ P : Subgroup G, (P : Set G) ⊆ W*(N : Set G)*W → P ≤ N) :
    SubgroupFreeSet ((QuotientGroup.mk' (N.subgroupOf (Subgroup.normalizer (N : Set G)))) ''
      ((Subgroup.normalizer (N : Set G)).subtype ⁻¹' W)) := by
  let H := (Subgroup.normalizer (N : Set G))
  let K := N.subgroupOf H
  let q := QuotientGroup.mk' K
  intro Q hQ
  let P := (Q.comap q).map H.subtype
  have hPW : (P : Set G) ⊆ W*(N : Set G)*W := by
    rintro x ⟨y,hy,rfl⟩
    have hyQ : q y ∈ Q := hy
    obtain ⟨w,hw,he⟩ := hQ hyQ
    have hkernel : w⁻¹*y ∈ K := (QuotientGroup.eq_one_iff _).1 (by
      change q (w⁻¹*y) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel])
    have hn : (w⁻¹*y).val ∈ N := hkernel
    refine ⟨w.val*(w⁻¹*y).val,⟨w.val,hw,(w⁻¹*y).val,hn,rfl⟩,1,hW1,?_⟩
    change (w.val*(w.val⁻¹*y.val))*1 = y.val
    simp only [mul_inv_cancel_left,mul_one]
  have hPN := htrap P hPW
  apply le_antisymm _ bot_le
  intro y hy
  obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective y
  apply Subgroup.mem_bot.mpr
  apply (QuotientGroup.eq_one_iff _).2
  change x.val ∈ N
  exact hPN (Subgroup.mem_map.mpr ⟨x,hy,rfl⟩)

/-- The algebraic normalization argument gives an open source and an NSS
quotient as soon as its symmetric window is an actual identity neighbourhood. -/
theorem subgroup_trapping_normalizer_quotient_nss [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) (W : Set G) (hWo : IsOpen W) (hW1 : (1 : G) ∈ W)
    (hWi : ∀ x ∈ W, x⁻¹ ∈ W)
    (htrap : ∀ P : Subgroup G, (P : Set G) ⊆ W*(N : Set G)*W → P ≤ N) :
    IsOpen ((Subgroup.normalizer (N : Set G)) : Set G) ∧ HasNoSmallSubgroups ((Subgroup.normalizer (N : Set G)) ⧸ N.subgroupOf (Subgroup.normalizer (N : Set G))) := by
  have hWN := subgroup_trapping_window_normalizes N W hWi htrap
  have hopen := (Subgroup.normalizer (N : Set G)).isOpen_of_mem_nhds
    (Filter.mem_of_superset (hWo.mem_nhds hW1) hWN)
  refine ⟨hopen,_,?_,?_,subgroup_trapping_normalizer_quotient_free N W hW1 htrap⟩
  · exact QuotientGroup.isOpenMap_coe _ (hWo.preimage continuous_subtype_val)
  · exact ⟨1,hW1,map_one (QuotientGroup.mk' (N.subgroupOf (Subgroup.normalizer (N : Set G))))⟩
end DirectedCycles
