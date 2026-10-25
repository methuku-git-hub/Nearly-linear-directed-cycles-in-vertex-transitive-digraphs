module

public import DirectedCycles.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs

@[expose] public section

set_option autoImplicit false
open scoped MonoidAlgebra
namespace DirectedCycles

/-- The coefficient-sum homomorphism of the integral group ring. -/
noncomputable def augmentation (G : Type*) [Group G] : ℤ[G] →+* ℤ :=
  MonoidAlgebra.liftNCRingHom (RingHom.id ℤ) (1 : G →* ℤ) (fun x _ => Commute.one_right x)

/-- The two-sided augmentation ideal. -/
noncomputable abbrev augmentationIdeal (G : Type*) [Group G] : Ideal ℤ[G] :=
  RingHom.ker (augmentation G)

/-- The actual truncated integral group ring Z[G]/I^D. -/
abbrev TruncatedGroupRing (G : Type*) [Group G] (D : ℕ) :=
  ℤ[G] ⧸ augmentationIdeal G ^ D

/-- The quotient map from the integral group ring. -/
noncomputable abbrev truncate (G : Type*) [Group G] (D : ℕ) : ℤ[G] →+* TruncatedGroupRing G D :=
  Ideal.Quotient.mk (augmentationIdeal G ^ D)

/-- The image of a group element in the truncated group ring. -/
noncomputable def truncatedElement (G : Type*) [Group G] (D : ℕ) : G →* TruncatedGroupRing G D :=
  (truncate G D).toMonoidHom.comp (MonoidAlgebra.of ℤ G)

@[simp] theorem augmentation_of {G : Type*} [Group G] (g : G) :
    augmentation G (MonoidAlgebra.of ℤ G g) = 1 := by
  simp [augmentation, MonoidAlgebra.of_apply]

theorem group_difference_mem_augmentation {G : Type*} [Group G] (g : G) :
    MonoidAlgebra.of ℤ G g - 1 ∈ augmentationIdeal G := by
  change augmentation G (MonoidAlgebra.of ℤ G g - 1) = 0
  rw [map_sub, augmentation_of, map_one, sub_self]

/-- The pure D-th power of every group difference vanishes in the quotient. -/
theorem truncated_difference_pow {G : Type*} [Group G] (D : ℕ) (g : G) :
    (truncatedElement G D g - 1)^D = 0 := by
  have h := Ideal.pow_mem_pow (group_difference_mem_augmentation g) D
  have hh := (Ideal.Quotient.eq_zero_iff_mem (I := augmentationIdeal G ^ D)).mpr h
  simp only [map_pow, map_sub, map_one] at hh
  exact hh

/-- Products of augmentation elements lie in the corresponding ideal power. -/
theorem list_prod_mem_augmentation_power {G : Type*} [Group G]
    (xs : List ℤ[G]) (hx : ∀ x ∈ xs, x ∈ augmentationIdeal G) :
    xs.prod ∈ augmentationIdeal G ^ xs.length := by
  induction xs with
  | nil => simp only [List.prod_nil, List.length_nil, Submodule.pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  | cons x xs ih =>
    rw [List.prod_cons, List.length_cons, Ideal.IsTwoSided.pow_succ]
    exact Ideal.mul_mem_mul (hx x (List.mem_cons_self ..))
      (ih (fun y hy => hx y (List.mem_cons_of_mem x hy)))

/-- Every ordered product of D group differences vanishes. -/
theorem truncated_difference_product {G : Type*} [Group G] (D : ℕ) (gs : List G)
    (hlen : gs.length = D) :
    (gs.map (fun g => truncatedElement G D g - 1)).prod = 0 := by
  have h := list_prod_mem_augmentation_power
    (gs.map (fun g => MonoidAlgebra.of ℤ G g - 1)) (by
      intro x hx
      obtain ⟨g,_,rfl⟩ := List.mem_map.mp hx
      exact group_difference_mem_augmentation g)
  rw [List.length_map, hlen] at h
  have hh := (Ideal.Quotient.eq_zero_iff_mem (I := augmentationIdeal G ^ D)).mpr h
  simp only [map_list_prod, List.map_map, Function.comp_def, map_sub, map_one] at hh
  exact hh

/-- Group elements generate the full quotient as an additive group. -/
theorem truncated_elements_generate {G : Type*} [Group G] (D : ℕ) :
    AddSubgroup.closure (Set.range (truncatedElement G D)) = ⊤ := by
  apply top_le_iff.mp
  intro x hx
  clear hx
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  induction a using MonoidAlgebra.induction_on with
  | of g => exact AddSubgroup.subset_closure ⟨g,rfl⟩
  | add a b ha hb =>
    rw [map_add]
    exact AddSubgroup.add_mem _ ha hb
  | smul z a ha =>
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ ha z

end DirectedCycles
