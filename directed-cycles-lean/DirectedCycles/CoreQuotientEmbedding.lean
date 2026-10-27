module

public import DirectedCycles.FiniteProductRanks
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

def coreConjugationHom {G : Type*} [Group G] (U : Subgroup G) (t : G) : U.normalCore →* U where
  toFun n := ⟨t⁻¹*n.val*t,by
    have h := (inferInstance : U.normalCore.Normal).conj_mem n.val n.property t⁻¹
    exact U.normalCore_le (by simpa only [inv_inv] using h)⟩
  map_one' := by apply Subtype.ext; dsimp; group
  map_mul' := by intro a b; apply Subtype.ext; dsimp; group

def coreProductHom {G : Type*} [Group G] (U H : Subgroup G) [(H.subgroupOf U).Normal]
    (t : (G ⧸ U) → G) : U.normalCore →* ((G ⧸ U) → U ⧸ H.subgroupOf U) :=
  MonoidHom.pi (fun q => (QuotientGroup.mk' (H.subgroupOf U)).comp (coreConjugationHom U (t q)))

/-- Intersecting all conjugates of H is precisely the kernel of the
finite product of conjugated quotient maps. This preserves a uniform
rank bound when making a finite-by-nilpotent subgroup normal. -/
theorem coreProductHom_kernel {G : Type*} [Group G] (U H : Subgroup G)
    [(H.subgroupOf U).Normal] (hnorm : U ≤ Subgroup.normalizer H)
    (t : (G ⧸ U) → G) (ht : ∀ q, Quotient.mk'' (t q) = q) :
    (coreProductHom U H t).ker = H.normalCore.comap U.normalCore.subtype := by
  ext n
  constructor
  · intro hn
    change ∀ b : G, b*n.val*b⁻¹ ∈ H
    intro b
    let q : G ⧸ U := Quotient.mk'' b⁻¹
    have hu : (t q)⁻¹*b⁻¹ ∈ U := QuotientGroup.leftRel_apply.mp (Quotient.exact (ht q))
    have hq := congrFun hn q
    have hm : (t q)⁻¹*n.val*t q ∈ H :=
      (QuotientGroup.eq_one_iff (coreConjugationHom U (t q) n)).mp hq
    have hh := (Subgroup.mem_normalizer_iff.mp (hnorm (U.inv_mem hu))
      ((t q)⁻¹*n.val*t q)).mp hm
    convert hh using 1
    group
  · intro hn
    change (coreProductHom U H t) n = 1
    funext q
    apply (QuotientGroup.eq_one_iff (coreConjugationHom U (t q) n)).mpr
    change (t q)⁻¹*n.val*t q ∈ H
    have hh : (t q)⁻¹*n.val*((t q)⁻¹)⁻¹ ∈ H := hn ((t q)⁻¹)
    rw [inv_inv] at hh
    exact hh

noncomputable def coreQuotientEquivRange {G : Type*} [Group G] (U H : Subgroup G)
    [(H.subgroupOf U).Normal] (hnorm : U ≤ Subgroup.normalizer H)
    (t : (G ⧸ U) → G) (ht : ∀ q, Quotient.mk'' (t q) = q) :
    (U.normalCore ⧸ H.normalCore.comap U.normalCore.subtype) ≃* (coreProductHom U H t).range :=
  (QuotientGroup.quotientMulEquivOfEq (coreProductHom_kernel U H hnorm t ht).symm).trans
    (QuotientGroup.quotientKerEquivRange (coreProductHom U H t))

/-- The normal core construction retains bounded rank and class. -/
theorem normal_core_nilpotent_quotient_bounds {G : Type*} [Group G] [Finite G]
    (U H : Subgroup G) [(H.subgroupOf U).Normal] [Group.IsNilpotent (U ⧸ H.subgroupOf U)]
    (hnorm : U ≤ Subgroup.normalizer H) (r c : ℕ)
    (hr : Group.rank (U ⧸ H.subgroupOf U) ≤ r)
    (hc : Group.nilpotencyClass (U ⧸ H.subgroupOf U) ≤ c) :
    Group.IsNilpotent (U.normalCore ⧸ H.normalCore.comap U.normalCore.subtype) ∧
    Group.rank (U.normalCore ⧸ H.normalCore.comap U.normalCore.subtype) ≤
      ∑ i ∈ Finset.range c, ((r+1)^U.index)^(i+1) ∧
    Group.nilpotencyClass (U.normalCore ⧸ H.normalCore.comap U.normalCore.subtype) ≤ c := by
  classical
  let : Fintype (G ⧸ U) := Fintype.ofFinite _
  let t : (G ⧸ U) → G := Quotient.out
  have ht : ∀ q, Quotient.mk'' (t q) = q := Quotient.out_eq
  let E := coreQuotientEquivRange U H hnorm t ht
  have hb := finite_power_nilpotent_subgroup_bounds r c hr hc (coreProductHom U H t).range
  have hcard : Fintype.card (G ⧸ U) = U.index := by
    rw [← Nat.card_eq_fintype_card]
    exact U.index_eq_card.symm
  rw [hcard] at hb
  refine ⟨Group.nilpotent_of_surjective E.symm.toMonoidHom E.symm.surjective,?_,?_⟩
  · exact (Group.rank_le_of_surjective E.symm.toMonoidHom E.symm.surjective).trans hb.1
  · exact (Group.nilpotencyClass_le_of_surjective E.symm.toMonoidHom E.symm.surjective).trans hb.2

end DirectedCycles
