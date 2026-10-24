import DirectedCycles.LocalGroupHom
import DirectedCycles.LocalPowerSequence

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A genuine global subgroup inside a local group: its multiplication is total
on the subset, and the subset contains the identity and all inverses. -/
structure IsGlobalSubgroup (S : Set G) : Prop where
  one_mem : L.one ∈ S
  inv_mem : ∀ x ∈ S, L.inv x ∈ S
  mul_total : ∀ x ∈ S, ∀ y ∈ S, ∃ z ∈ S, L.mulRel x y z

namespace IsGlobalSubgroup
variable {L} {S : Set G} (hS : L.IsGlobalSubgroup S)

noncomputable def mul (a b : S) : S :=
  ⟨Classical.choose (hS.mul_total a.val a.property b.val b.property),
    (Classical.choose_spec (hS.mul_total a.val a.property b.val b.property)).1⟩

theorem mul_spec (a b : S) : L.mulRel a.val b.val (hS.mul a b).val :=
  (Classical.choose_spec (hS.mul_total a.val a.property b.val b.property)).2

/-- The subgroup predicate constructs an actual Lean group, so global
subgroups are not represented by an unproved group-structure assumption. -/
@[instance_reducible]
noncomputable def toGroup : Group S where
  one := ⟨L.one,hS.one_mem⟩
  mul := hS.mul
  inv a := ⟨L.inv a.val,hS.inv_mem a.val a.property⟩
  mul_assoc a b c := Subtype.ext (L.assoc (hS.mul_spec a b) (hS.mul_spec b c)
    (hS.mul_spec (hS.mul a b) c) (hS.mul_spec a (hS.mul b c)))
  one_mul a := Subtype.ext (L.unique (hS.mul_spec ⟨L.one,hS.one_mem⟩ a) (L.one_mul a.val))
  mul_one a := Subtype.ext (L.unique (hS.mul_spec a ⟨L.one,hS.one_mem⟩) (L.mul_one a.val))
  inv_mul_cancel a := Subtype.ext (L.unique
    (hS.mul_spec ⟨L.inv a.val,hS.inv_mem a.val a.property⟩ a) (L.inv_mul a.val))

noncomputable def inclusionHom :
    letI := hS.toGroup
    LocalGroupHom (ofGroup S) L := by
  letI := hS.toGroup
  refine ⟨Subtype.val,rfl,fun _ => rfl,?_⟩
  intro a b c h
  have hh := hS.mul_spec a b
  change a*b = c at h
  change L.mulRel a.val b.val (a*b).val at hh
  simpa only [h] using hh
end IsGlobalSubgroup

/-- NSS excludes actual global subgroups entirely contained in A. -/
def IsNSS (A : Set G) : Prop := ∀ S : Set G, L.IsGlobalSubgroup S → S ⊆ A → S ⊆ {L.one}

theorem PowerSequence.range_isGlobalSubgroup [Finite G] (hL : L.Cancellative)
    {g : G} (p : L.PowerSequence g) : L.IsGlobalSubgroup (Set.range p.power) := by
  obtain ⟨h1,hi,hm⟩ := p.range_closed hL
  exact ⟨h1,hi,hm⟩

/-- The finite NSS condition is equivalent to excluding every nonidentity
complete sequence of powers inside A. -/
theorem finite_nss_iff_powerSequence [Finite G] (hL : L.Cancellative) (A : Set G) :
    L.IsNSS A ↔ ∀ g : G, ∀ p : L.PowerSequence g, (∀ n, p.power n ∈ A) → g = L.one := by
  constructor
  · intro hNSS g p hp
    have hsub : Set.range p.power ⊆ A := by rintro x ⟨n,rfl⟩; exact hp n
    have hg : g ∈ Set.range p.power := ⟨1,p.one⟩
    exact hNSS _ (p.range_isGlobalSubgroup L hL) hsub hg
  · intro h S hS hSA x hx
    let := hS.toGroup
    let xS : S := ⟨x,hx⟩
    let p : L.PowerSequence x := {
      power := fun n => ((xS^n : S) : G)
      product := by
        intro n
        have hp := (ofGroup_product S (List.replicate n xS)).map hS.inclusionHom
        simpa [IsGlobalSubgroup.inclusionHom,xS] using hp }
    exact h x p (fun n => hSA (xS^n).property)
end LocalGroupAlgebra
end DirectedCycles
