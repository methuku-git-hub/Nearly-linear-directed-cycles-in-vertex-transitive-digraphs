module

public import DirectedCycles.LocalGroupCongruence
public import DirectedCycles.LocalDivision
public import DirectedCycles.LocalGlobalSubgroup
public import DirectedCycles.LocalTwoProducts

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A symmetric neighbourhood saturated by a genuine normal subgroup. Only
binary products of neighbourhood elements are required in the ambient local
group; their values need not stay in the neighbourhood. -/
structure NormalSubgroupWindow (H S : Set G) : Prop where
  subgroup : L.IsGlobalSubgroup H
  subset : H ⊆ S
  inv_mem : ∀ s ∈ S, L.inv s ∈ S
  binary : ∀ a ∈ S, ∀ b ∈ S, L.Defined a b
  saturated : ∀ h ∈ H, ∀ s ∈ S, ∃ z ∈ S, L.mulRel h s z
  normal : ∀ s ∈ S, ∀ h ∈ H, ∃ k ∈ H, ∃ t, L.mulRel s h t ∧ L.mulRel k s t

namespace NormalSubgroupWindow
variable {L} {H S : Set G} (W : L.NormalSubgroupWindow H S)

abbrev one_mem : L.one ∈ S := W.subset W.subgroup.one_mem
abbrev restricted := L.restrict S W.one_mem W.inv_mem

def relation (_W : L.NormalSubgroupWindow H S) (a b : S) : Prop := ∃ h ∈ H, L.mulRel h b.val a.val

theorem relation_refl (a : S) : W.relation a a :=
  ⟨L.one,W.subgroup.one_mem,L.one_mul a.val⟩

theorem relation_symm (hd : L.DivisionClosed) {a b : S} (h : W.relation a b) :
    W.relation b a := by
  obtain ⟨g,hg,hm⟩ := h
  exact ⟨L.inv g,W.subgroup.inv_mem g hg,hd.left hm⟩

theorem relation_trans {a b c : S} (hab : W.relation a b) (hbc : W.relation b c) :
    W.relation a c := by
  obtain ⟨h,hh,hm⟩ := hab
  obtain ⟨k,hk,hkbc⟩ := hbc
  obtain ⟨p,hp,hkp⟩ := W.subgroup.mul_total h hh k hk
  obtain ⟨z,hz⟩ := W.binary p (W.subset hp) c.val c.property
  have he : z = a.val := L.assoc hkp hkbc hz hm
  exact ⟨p,hp,he ▸ hz⟩

def setoid (hd : L.DivisionClosed) : Setoid S where
  r := W.relation
  iseqv := ⟨W.relation_refl,W.relation_symm hd,W.relation_trans⟩

theorem relation_inv (hr : L.Reversible) {a b : S} (hab : W.relation a b) :
    W.relation (W.restricted.inv a) (W.restricted.inv b) := by
  obtain ⟨h,hh,hm⟩ := hab
  obtain ⟨k,hk,t,ht,ht'⟩ := W.normal (L.inv b.val) (W.inv_mem b.val b.property)
    (L.inv h) (W.subgroup.inv_mem h hh)
  have he : t = L.inv a.val := L.unique ht (hr hm)
  refine ⟨k,hk,?_⟩
  change L.mulRel k (L.inv b.val) (L.inv a.val)
  exact he ▸ ht'

/-- Changing the left representative transports its product back into the
saturated neighbourhood, by an ambient product and defined associativity. -/
theorem transport_left {a b c a' : S} (hm : L.mulRel a.val b.val c.val)
    (ha : W.relation a' a) :
    ∃ c' : S, L.mulRel a'.val b.val c'.val ∧ W.relation c' c := by
  obtain ⟨h,hh,hha⟩ := ha
  obtain ⟨z,hz,hzc⟩ := W.saturated h hh c.val c.property
  obtain ⟨v,hv⟩ := W.binary a'.val a'.property b.val b.property
  have he : v = z := L.assoc hha hm hv hzc
  exact ⟨⟨z,hz⟩,he ▸ hv,h,hh,hzc⟩

/-- Normality moves the changed right representative to a left factor in H.
Every intermediate product is justified in the original local group. -/
theorem transport_right {a b c b' : S} (hm : L.mulRel a.val b.val c.val)
    (hb : W.relation b' b) :
    ∃ c' : S, L.mulRel a.val b'.val c'.val ∧ W.relation c' c := by
  obtain ⟨h,hh,hhb⟩ := hb
  obtain ⟨k,hk,t,hah,hka⟩ := W.normal a.val a.property h hh
  obtain ⟨t',ht',hkt⟩ := W.saturated k hk a.val a.property
  have het : t = t' := L.unique hka hkt
  obtain ⟨z,hz,hzc⟩ := W.saturated k hk c.val c.property
  obtain ⟨v,hv⟩ := W.binary t' ht' b.val b.property
  have hvz : v = z := L.assoc hkt hm hv hzc
  have htz : L.mulRel t b.val z := by simpa only [het,hvz] using hv
  obtain ⟨w,hw⟩ := W.binary a.val a.property b'.val b'.property
  have hzw : z = w := L.assoc hah hhb htz hw
  exact ⟨⟨z,hz⟩,hzw.symm ▸ hw,k,hk,hzc⟩

/-- The actual orbit relation is a local-group congruence, including transport
of product domains under every choice of representatives. -/
def congruence (hd : L.DivisionClosed) (hr : L.Reversible) :
    LocalGroupCongruence W.restricted where
  toSetoid := W.setoid hd
  inv_rel := W.relation_inv hr
  mul_lift := by
    intro a b c a' b' hm ha hb
    obtain ⟨d,hdm,hda⟩ := W.transport_left hm (W.relation_symm hd ha)
    obtain ⟨e,hem,hed⟩ := W.transport_right hdm (W.relation_symm hd hb)
    exact ⟨e,hem,W.relation_symm hd (W.relation_trans hed hda)⟩
end NormalSubgroupWindow
end LocalGroupAlgebra
end DirectedCycles
