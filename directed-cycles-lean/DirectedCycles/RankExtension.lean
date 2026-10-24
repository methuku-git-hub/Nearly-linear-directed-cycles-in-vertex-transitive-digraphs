import DirectedCycles.Basic
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- Generators of a normal subgroup and lifts of generators of its quotient
together generate the ambient group. -/
theorem rank_le_normal_add_quotient {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] : Group.rank G ≤ Group.rank N + Group.rank (G ⧸ N) := by
  obtain ⟨S, hScard, hS⟩ := Group.rank_spec N
  obtain ⟨T, hTcard, hT⟩ := Group.rank_spec (G ⧸ N)
  let q := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  let lift : G ⧸ N → G := fun x => Classical.choose (hq x)
  have hlift : ∀ x, q (lift x) = x := fun x => Classical.choose_spec (hq x)
  let W := S.image N.subtype ∪ T.image lift
  let K := Subgroup.closure (W : Set G)
  have hNK : N ≤ K := by
    have hNS : Subgroup.closure (N.subtype '' (S : Set N)) = N := by
      rw [← MonoidHom.map_closure, hS, Subgroup.map_top, Subgroup.subtype_range]
    rw [← hNS]
    apply Subgroup.closure_mono
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  have hmap : K.map q = ⊤ := by
    apply top_unique
    rw [← hT]
    apply (K.map q).closure_le.mpr
    intro x hx
    refine ⟨lift x, ?_, hlift x⟩
    exact Subgroup.subset_closure (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  have hK : K = ⊤ := by
    have hk : q.ker ≤ K := by simpa only [q, QuotientGroup.ker_mk'] using hNK
    rw [← Subgroup.comap_map_eq_self hk, hmap, Subgroup.comap_top]
  have hc : W.card ≤ S.card + T.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
  exact (Group.rank_le hK).trans (by simpa only [hScard, hTcard] using hc)

/-- A bounded set of lifts generates modulo the normal subgroup. -/
theorem quotient_generators_lift {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] :
    ∃ S : Finset G, S.card ≤ Group.rank (G ⧸ N) ∧ Subgroup.closure (S : Set G) ⊔ N = ⊤ := by
  obtain ⟨T, hTcard, hT⟩ := Group.rank_spec (G ⧸ N)
  let q := QuotientGroup.mk' N
  let lift : G ⧸ N → G := fun x => Classical.choose (QuotientGroup.mk'_surjective N x)
  have hlift : ∀ x, q (lift x) = x := fun x => Classical.choose_spec (QuotientGroup.mk'_surjective N x)
  let S := T.image lift
  refine ⟨S, Finset.card_image_le.trans_eq hTcard, ?_⟩
  have hmap : (Subgroup.closure (S : Set G)).map q = ⊤ := by
    apply top_unique
    rw [← hT]
    apply ((Subgroup.closure (S : Set G)).map q).closure_le.mpr
    intro x hx
    exact ⟨lift x, Subgroup.subset_closure (Finset.mem_image.mpr ⟨x,hx,rfl⟩), hlift x⟩
  have h := Subgroup.comap_map_eq q (Subgroup.closure (S : Set G))
  rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
  exact h.symm

end DirectedCycles
