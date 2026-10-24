import DirectedCycles.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Rank

set_option autoImplicit false
namespace DirectedCycles

/-- The image of A in G/B is canonically A/(A intersect B). -/
noncomputable def subgroupQuotientEquivMap {G : Type*} [Group G]
    (A B : Subgroup G) [B.Normal] :
    A ⧸ B.subgroupOf A ≃* A.map (QuotientGroup.mk' B) := by
  let q := QuotientGroup.mk' B
  let f : A →* A.map q := {
    toFun := fun x => ⟨q x.val, ⟨x.val, x.property, rfl⟩⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' := fun x y => Subtype.ext (map_mul q x.val y.val) }
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, he⟩ := y.property
    exact ⟨⟨x,hx⟩, Subtype.ext he⟩
  have hk : f.ker = B.subgroupOf A := by
    ext x
    change f x = 1 ↔ x.val ∈ B
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff x.val
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hs)

/-- A surjective group homomorphism induces a surjection of abelianizations. -/
theorem abelianization_map_surjective {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) : Function.Surjective (Abelianization.map f) := by
  intro a
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (commutator Q) a
  obtain ⟨g, rfl⟩ := hf q
  exact ⟨Abelianization.of g, rfl⟩

theorem abelianization_exponent_of_surjective {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (e : ℕ)
    (he : ∀ a : Abelianization G, a ^ e = 1) :
    ∀ a : Abelianization Q, a ^ e = 1 := by
  intro a
  obtain ⟨b, rfl⟩ := abelianization_map_surjective f hf a
  rw [← map_pow, he, map_one]

/-- The canonical surjection from a subgroup onto its image. -/
def subgroupMapHom {G Q : Type*} [Group G] [Group Q] (f : G →* Q) (A : Subgroup G) :
    A →* A.map f where
  toFun x := ⟨f x.val, ⟨x.val,x.property,rfl⟩⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f x.val y.val)

theorem subgroupMapHom_surjective {G Q : Type*} [Group G] [Group Q] (f : G →* Q) (A : Subgroup G) :
    Function.Surjective (subgroupMapHom f A) := by
  intro y
  obtain ⟨x,hx,he⟩ := y.property
  exact ⟨⟨x,hx⟩, Subtype.ext he⟩

/-- Every homomorphism induces the expected map between subquotients. -/
def subgroupQuotientMap {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    (A B : Subgroup G) [B.Normal] [(B.map f).Normal] :
    A ⧸ B.subgroupOf A →* (A.map f) ⧸ (B.map f).subgroupOf (A.map f) :=
  QuotientGroup.lift (B.subgroupOf A)
    ((QuotientGroup.mk' ((B.map f).subgroupOf (A.map f))).comp (subgroupMapHom f A)) (by
      intro x hx
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨x.val,hx,rfl⟩)

theorem subgroupQuotientMap_surjective {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    (A B : Subgroup G) [B.Normal] [(B.map f).Normal] :
    Function.Surjective (subgroupQuotientMap f A B) := by
  intro y
  obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective ((B.map f).subgroupOf (A.map f)) y
  obtain ⟨x,rfl⟩ := subgroupMapHom_surjective f A z
  exact ⟨QuotientGroup.mk x,rfl⟩

end DirectedCycles
