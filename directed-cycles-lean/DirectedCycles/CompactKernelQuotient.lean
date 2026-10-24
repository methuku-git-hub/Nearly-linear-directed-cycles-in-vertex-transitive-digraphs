import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Maps.Proper.Basic

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual quotient by a compact normal subgroup is a proper map.
Compactness of its fibres is proved using their literal coset descriptions. -/
theorem compact_kernel_quotient_proper (N : Subgroup G) [N.Normal]
    (hN : IsCompact (N : Set G)) : IsProperMap (QuotientGroup.mk' N) := by
  let q := QuotientGroup.mk' N
  refine isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨QuotientGroup.continuous_mk,QuotientGroup.isClosedMap_coe hN,?_⟩
  intro y
  obtain ⟨a,rfl⟩ := QuotientGroup.mk_surjective y
  have he : q ⁻¹' {q a} = (fun x : G => a*x) '' (N : Set G) := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxq : q x = q a := hx
      have hn : a⁻¹*x ∈ N := (QuotientGroup.eq_one_iff _).1 (by
        change q (a⁻¹*x) = 1
        rw [map_mul,map_inv,hxq,inv_mul_cancel])
      exact ⟨a⁻¹*x,hn,mul_inv_cancel_left a x⟩
    · rintro x ⟨b,hb,rfl⟩
      change q (a*b) = q a
      rw [map_mul,show q b = 1 from (QuotientGroup.eq_one_iff _).2 hb,mul_one]
  change IsCompact (q ⁻¹' {q a})
  rw [he]
  exact hN.image (continuous_const.mul continuous_id)

/-- A closed map has a target neighbourhood whose entire preimage lies in
any open set containing the relevant fibre. -/
theorem closed_map_small_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y) (hq : IsClosedMap q) (y : Y) (O : Set X)
    (hO : IsOpen O) (hf : q ⁻¹' {y} ⊆ O) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ q ⁻¹' V ⊆ O := by
  refine ⟨(q '' Oᶜ)ᶜ,(hq _ hO.isClosed_compl).isOpen_compl,?_,?_⟩
  · rintro ⟨x,hx,he⟩
    exact hx (hf he)
  · intro x hx
    by_contra hn
    exact hx ⟨x,hn,rfl⟩

/-- Compact-kernel quotients preserve the small-preimage part of a good
model after shrinking its target neighbourhood. -/
theorem compact_kernel_quotient_small_preimage (N : Subgroup G) [N.Normal]
    (hN : IsCompact (N : Set G)) (O : Set G) (hO : IsOpen O)
    (hNO : (N : Set G) ⊆ O) :
    ∃ V : Set (G ⧸ N), IsOpen V ∧ (1 : G ⧸ N) ∈ V ∧
      (QuotientGroup.mk' N) ⁻¹' V ⊆ O := by
  apply closed_map_small_preimage (QuotientGroup.mk' N)
    (QuotientGroup.isClosedMap_coe hN) 1 O hO
  intro x hx
  exact hNO ((QuotientGroup.eq_one_iff _).1 hx)
end DirectedCycles
