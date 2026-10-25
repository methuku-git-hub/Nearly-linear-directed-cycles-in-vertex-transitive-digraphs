module

public import DirectedCycles.Basic
public import DirectedCycles.RankExtension
public import DirectedCycles.NormalClosureExponent
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Rank

@[expose] public section

set_option autoImplicit false
open scoped commutatorElement Classical IsMulCommutative
namespace DirectedCycles

/-- Conjugation is trivial on a central commutator. -/
theorem conjugate_central_commutator {G : Type*} [Group G] (H : Subgroup G)
    (hcentral : ⁅H, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G)
    (x : H) (y g : G) : g * ⁅x.val, y⁆ * g⁻¹ = ⁅x.val, y⁆ := by
  have hc := hcentral (Subgroup.commutator_mem_commutator x.property (Subgroup.mem_top y))
  rw [Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_right]

/-- With central commutator values, the commutator is a homomorphism in its
second entry, with values in the center. -/
def centralCommutatorRightHom {G : Type*} [Group G] (H : Subgroup G)
    (hcentral : ⁅H, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G) (x : H) : G →* Subgroup.center G where
  toFun y := ⟨⁅x.val, y⁆, hcentral (Subgroup.commutator_mem_commutator x.property (Subgroup.mem_top y))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' y z := Subtype.ext (by
    change ⁅x.val, y * z⁆ = ⁅x.val, y⁆ * ⁅x.val, z⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    calc ⁅x.val, y⁆ * y * ⁅x.val, z⁆ * y⁻¹ = ⁅x.val, y⁆ * (y * ⁅x.val, z⁆ * y⁻¹) := by group
         _ = ⁅x.val, y⁆ * ⁅x.val, z⁆ := by rw [conjugate_central_commutator H hcentral])

/-- The corresponding homomorphism in the first entry. -/
def centralCommutatorLeftHom {G : Type*} [Group G] (H : Subgroup G)
    (hcentral : ⁅H, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G) (y : G) : H →* Subgroup.center G where
  toFun x := ⟨⁅x.val, y⁆, hcentral (Subgroup.commutator_mem_commutator x.property (Subgroup.mem_top y))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x z := Subtype.ext (by
    change ⁅x.val * z.val, y⁆ = ⁅x.val, y⁆ * ⁅z.val, y⁆
    rw [commutatorElement_mul_left_eq_conj_mul, conjugate_central_commutator H hcentral z y x.val]
    exact Subgroup.mem_center_iff.mp
      (hcentral (Subgroup.commutator_mem_commutator x.property (Subgroup.mem_top y))) _)

/-- Multilinearity makes every value have exponent dividing that of the
abelianization of the second argument group. -/
theorem central_commutator_exponent {G : Type*} [Group G] (H : Subgroup G)
    (hcentral : ⁅H, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G) (e : ℕ)
    (he : ∀ a : Abelianization G, a ^ e = 1) (x : H) (y : G) : ⁅x.val, y⁆ ^ e = 1 := by
  let f := centralCommutatorRightHom H hcentral x
  let F := Abelianization.lift f
  have hy : F (Abelianization.of y) ^ e = 1 := by rw [← map_pow, he, map_one]
  have h : f y ^ e = 1 := by simpa only [F, Abelianization.lift_apply_of] using hy
  exact congrArg Subtype.val h

/-- Finite generating sets suffice in both entries of a central commutator.
The first entry may be generated modulo any subgroup of the ambient center. -/
theorem central_commutator_generators {G : Type*} [Group G] (H : Subgroup G)
    (hcentral : ⁅H, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G)
    (Z : Subgroup H) (hZ : ∀ z : Z, z.val.val ∈ Subgroup.center G)
    (S : Finset H) (T : Finset G)
    (hS : Subgroup.closure (S : Set H) ⊔ Z = ⊤)
    (hT : Subgroup.closure (T : Set G) = ⊤) :
    ⁅H, (⊤ : Subgroup G)⁆ =
      Subgroup.closure (((S ×ˢ T).image (fun p => ⁅p.1.val, p.2⁆)) : Set G) := by
  let K := Subgroup.closure (((S ×ˢ T).image (fun p => ⁅p.1.val, p.2⁆)) : Set G)
  have hgen : ∀ s ∈ S, ∀ t ∈ T, ⁅s.val, t⁆ ∈ K := by
    intro s hs t ht
    exact Subgroup.subset_closure (Finset.mem_image.mpr ⟨(s,t), Finset.mem_product.mpr ⟨hs,ht⟩, rfl⟩)
  have hr : ∀ s ∈ S, ∀ y : G, ⁅s.val, y⁆ ∈ K := by
    intro s hs y
    let f := (Subgroup.center G).subtype.comp (centralCommutatorRightHom H hcentral s)
    have hle : Subgroup.closure (T : Set G) ≤ K.comap f := (K.comap f).closure_le.mpr (hgen s hs)
    rw [hT] at hle
    exact hle (Subgroup.mem_top y)
  have hall : ∀ x : H, ∀ y : G, ⁅x.val, y⁆ ∈ K := by
    intro x y
    let f := (Subgroup.center G).subtype.comp (centralCommutatorLeftHom H hcentral y)
    have hle : Subgroup.closure (S : Set H) ⊔ Z ≤ K.comap f := by
      apply sup_le
      · exact (K.comap f).closure_le.mpr (fun s hs => hr s hs y)
      · intro z hz
        change ⁅z.val, y⁆ ∈ K
        have hz1 : ⁅z.val, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_center_iff.mp (hZ ⟨z,hz⟩) y).symm
        rw [hz1]
        exact K.one_mem
    rw [hS] at hle
    exact hle (Subgroup.mem_top x)
  apply le_antisymm
  · exact Subgroup.commutator_le.mpr (fun x hx y _ => hall ⟨x,hx⟩ y)
  · apply (⁅H, (⊤ : Subgroup G)⁆).closure_le.mpr
    intro g hg
    obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp hg
    exact Subgroup.commutator_mem_commutator x.property (Subgroup.mem_top y)

/-- The product bound for the number of central commutator generators. -/
theorem central_commutator_rank_le {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hcentral : ⁅H, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G)
    (Z : Subgroup H) [Z.Normal] (hZ : ∀ z : Z, z.val.val ∈ Subgroup.center G) :
    Group.rank (⁅H, (⊤ : Subgroup G)⁆ : Subgroup G) ≤ Group.rank (H ⧸ Z) * Group.rank G := by
  obtain ⟨S, hScard, hS⟩ := quotient_generators_lift Z
  obtain ⟨T, hTcard, hT⟩ := Group.rank_spec G
  have hgen := central_commutator_generators H hcentral Z hZ S T hS hT
  rw [Subgroup.rank_congr hgen]
  apply (Subgroup.rank_closure_finset_le_card _).trans
  apply Finset.card_image_le.trans
  rw [Finset.card_product, hTcard]
  exact Nat.mul_le_mul_right _ hScard

/-- The whole central commutator subgroup inherits the abelianization's
exponent, not only individual commutators. -/
theorem central_commutator_subgroup_exponent {G : Type*} [Group G] (H : Subgroup G)
    (hcentral : ⁅H, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G) (e : ℕ)
    (he : ∀ a : Abelianization G, a ^ e = 1) :
    ∀ x : (⁅H, (⊤ : Subgroup G)⁆ : Subgroup G), x ^ e = 1 := by
  let S : Set G := {g | ∃ x ∈ H, ∃ y : G, ⁅x,y⁆ = g}
  let K := ⁅H, (⊤ : Subgroup G)⁆
  have hK : K = Subgroup.closure S := by simp only [K, Subgroup.commutator_def, Subgroup.mem_top, true_and, S]
  let f : K →* Subgroup.center G := {
    toFun := fun x => ⟨x.val, hcentral x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hgen : Subgroup.closure (K.subtype ⁻¹' S) = ⊤ := by
    subst K
    rw [hK]
    exact Subgroup.closure_preimage_eq_top S
  have hp : ∀ x ∈ K.subtype ⁻¹' S, f x ^ e = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hab⟩ := hx
    change ⁅a,b⁆ = x.val at hab
    apply Subtype.ext
    change x.val ^ e = 1
    rw [← hab]
    exact central_commutator_exponent H hcentral e he ⟨a,ha⟩ b
  intro x
  have h := commutative_image_exponent_of_generators f (K.subtype ⁻¹' S) hgen e hp x
  apply Subtype.ext
  exact congrArg (fun z : Subgroup.center G => z.val) h

end DirectedCycles
