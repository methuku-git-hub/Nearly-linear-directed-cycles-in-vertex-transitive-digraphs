module

public import DirectedCycles.Augmentation
public import Mathlib.Algebra.Group.Subgroup.Map

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Coefficient sum descends through I^D for positive D. -/
noncomputable def truncatedAugmentation {G : Type*} [Group G] (D : ℕ) (hD : 0 < D) :
    TruncatedGroupRing G D →+* ℤ :=
  Ideal.Quotient.lift (augmentationIdeal G ^ D) (augmentation G)
    (fun _ hx => Ideal.pow_le_self (Nat.ne_zero_of_lt hD) hx)

@[simp] theorem truncatedAugmentation_truncate {G : Type*} [Group G]
    (D : ℕ) (hD : 0 < D) (x : MonoidAlgebra ℤ G) :
    truncatedAugmentation D hD (truncate G D x) = augmentation G x := rfl

@[simp] theorem truncatedAugmentation_element {G : Type*} [Group G]
    (D : ℕ) (hD : 0 < D) (g : G) :
    truncatedAugmentation D hD (truncatedElement G D g) = 1 := augmentation_of g

/-- The actual Passi polynomial group, realized as the zero-augmentation
subgroup of Z[G]/I^D. -/
noncomputable def passiGroup {G : Type*} [Group G] (D : ℕ) (hD : 0 < D) :
    AddSubgroup (TruncatedGroupRing G D) := (truncatedAugmentation D hD).toAddMonoidHom.ker

/-- This subgroup is exactly the image of the augmentation ideal under
truncation, namely the usual I/I^D realization. -/
theorem passiGroup_eq_augmentation_image {G : Type*} [Group G] (D : ℕ) (hD : 0 < D) :
    passiGroup (G := G) D hD = (augmentationIdeal G).toAddSubgroup.map (truncate G D).toAddMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a,hx,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    exact ha

/-- Projection along the free coefficient-sum summand, based at any group
element e₀. Its image on e is exactly e-e₀. -/
noncomputable def passiProjection {G : Type*} [Group G] (D : ℕ) (hD : 0 < D) (e₀ : G) :
    TruncatedGroupRing G D →+ passiGroup (G := G) D hD where
  toFun x := ⟨x - truncatedAugmentation D hD x • truncatedElement G D e₀, by
    change truncatedAugmentation D hD (x - truncatedAugmentation D hD x • truncatedElement G D e₀) = 0
    simp⟩
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by
    simp only [map_add,add_zsmul,AddSubgroup.coe_add]
    abel)

theorem passiProjection_fixed {G : Type*} [Group G] (D : ℕ) (hD : 0 < D) (e₀ : G)
    (x : passiGroup (G := G) D hD) : passiProjection D hD e₀ x.val = x := by
  apply Subtype.ext
  change x.val - truncatedAugmentation D hD x.val • truncatedElement G D e₀ = x.val
  have hx : truncatedAugmentation D hD x.val = 0 := x.property
  rw [hx,zero_zsmul,sub_zero]

theorem passiProjection_surjective {G : Type*} [Group G] (D : ℕ) (hD : 0 < D) (e₀ : G) :
    Function.Surjective (passiProjection (G := G) D hD e₀) :=
  fun x => ⟨x.val,passiProjection_fixed D hD e₀ x⟩

@[simp] theorem passiProjection_element {G : Type*} [Group G] (D : ℕ) (hD : 0 < D)
    (e₀ g : G) : (passiProjection D hD e₀ (truncatedElement G D g)).val =
      truncatedElement G D g - truncatedElement G D e₀ := by
  change truncatedElement G D g - truncatedAugmentation D hD (truncatedElement G D g) •
    truncatedElement G D e₀ = _
  rw [truncatedAugmentation_element,one_zsmul]

/-- The differences g-e₀ generate the Passi group. -/
theorem passiProjection_generates {G : Type*} [Group G] (D : ℕ) (hD : 0 < D) (e₀ : G) :
    AddSubgroup.closure (Set.range (fun g => passiProjection D hD e₀ (truncatedElement G D g))) = ⊤ := by
  change AddSubgroup.closure (Set.range ((passiProjection D hD e₀) ∘ (truncatedElement G D))) = ⊤
  rw [Set.range_comp,← AddMonoidHom.map_closure,truncated_elements_generate]
  exact AddSubgroup.map_top_of_surjective _ (passiProjection_surjective D hD e₀)

noncomputable def passiDifferences {G : Type*} [Group G] (D : ℕ) (hD : 0 < D)
    (E : Set G) (e₀ : G) : AddSubgroup (passiGroup (G := G) D hD) :=
  AddSubgroup.closure ((fun g => passiProjection D hD e₀ (truncatedElement G D g)) '' E)

/-- The augmentation multiplier descends to the difference subgroup, preserving
its exact value, without a torsion-free assumption. -/
theorem passi_multiplier_of_augmentation {G : Type*} [Group G] (D : ℕ) (hD : 0 < D)
    (E : Set G) (e₀ : G) (M : ℕ)
    (hM : ∀ x : TruncatedGroupRing G D,
      M • x ∈ AddSubgroup.closure (truncatedElement G D '' E)) :
    ∀ x : passiGroup (G := G) D hD, M • x ∈ passiDifferences D hD E e₀ := by
  intro x
  have hm : passiProjection D hD e₀ (M • x.val) ∈
      (AddSubgroup.closure (truncatedElement G D '' E)).map (passiProjection D hD e₀) :=
    ⟨M • x.val,hM x.val,rfl⟩
  rw [AddMonoidHom.map_closure,Set.image_image] at hm
  change passiProjection D hD e₀ (M • x.val) ∈ passiDifferences D hD E e₀ at hm
  rwa [map_nsmul,passiProjection_fixed] at hm

/-- For e₀ in E the two multiplier formulations are equivalent. -/
theorem augmentation_multiplier_iff_passi {G : Type*} [Group G] (D : ℕ) (hD : 0 < D)
    (E : Set G) (e₀ : G) (he₀ : e₀ ∈ E) (M : ℕ) :
    (∀ x : TruncatedGroupRing G D,
      M • x ∈ AddSubgroup.closure (truncatedElement G D '' E)) ↔
    (∀ x : passiGroup (G := G) D hD, M • x ∈ passiDifferences D hD E e₀) := by
  constructor
  · exact passi_multiplier_of_augmentation D hD E e₀ M
  · intro hM x
    let W := AddSubgroup.closure (truncatedElement G D '' E)
    have he : truncatedElement G D e₀ ∈ W := AddSubgroup.subset_closure ⟨e₀,he₀,rfl⟩
    have hle : passiDifferences D hD E e₀ ≤
        W.comap (passiGroup (G := G) D hD).subtype := by
      apply (W.comap _).closure_le.mpr
      rintro y ⟨g,hg,rfl⟩
      change (passiProjection D hD e₀ (truncatedElement G D g)).val ∈ W
      rw [passiProjection_element]
      exact W.sub_mem (AddSubgroup.subset_closure ⟨g,hg,rfl⟩) he
    have hp := hle (hM (passiProjection D hD e₀ x))
    have hb := W.nsmul_mem (W.zsmul_mem he (truncatedAugmentation D hD x)) M
    have heq : M • x = M • (passiProjection D hD e₀ x).val +
        M • (truncatedAugmentation D hD x • truncatedElement G D e₀) := by
      change M • x = M • (x - truncatedAugmentation D hD x • truncatedElement G D e₀) + _
      rw [smul_sub,sub_add_cancel]
    rw [heq]
    exact W.add_mem hp hb

end DirectedCycles
