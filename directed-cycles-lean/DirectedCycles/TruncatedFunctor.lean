module

public import DirectedCycles.Augmentation
public import Mathlib.Algebra.MonoidAlgebra.MapDomain

@[expose] public section

set_option autoImplicit false
open scoped MonoidAlgebra
namespace DirectedCycles

/-- Ring maps carry ideal powers into powers whenever they carry the ideals. -/
theorem ringHom_mem_ideal_power {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S) (h : ∀ x ∈ I, f x ∈ J) (n : ℕ) :
    ∀ x ∈ I ^ n, f x ∈ J ^ n := by
  induction n with
  | zero => intro x _; rw [Submodule.pow_zero,Ideal.one_eq_top]; exact Submodule.mem_top
  | succ n ih =>
    intro x hx
    rw [Submodule.pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [map_mul]
      exact Ideal.mul_mem_mul (ih a ha) (h b hb)
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy

/-- A group homomorphism induces the usual map of integral group rings. -/
noncomputable abbrev groupRingMap {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) : ℤ[G] →+* ℤ[Q] := MonoidAlgebra.mapDomainRingHom ℤ f

@[simp] theorem groupRingMap_of {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (g : G) :
    groupRingMap f (MonoidAlgebra.of ℤ G g) = MonoidAlgebra.of ℤ Q (f g) := by
  simp [groupRingMap, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.of_apply]

theorem augmentation_groupRingMap {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (x : ℤ[G]) : augmentation Q (groupRingMap f x) = augmentation G x := by
  induction x using MonoidAlgebra.induction_on with
  | of g => rw [groupRingMap_of, augmentation_of, augmentation_of]
  | add x y hx hy => simp only [map_add,hx,hy]
  | smul z x hx => simp only [map_zsmul,hx]

theorem groupRingMap_augmentation_power {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (D : ℕ) (x : ℤ[G]) (hx : x ∈ augmentationIdeal G ^ D) :
    groupRingMap f x ∈ augmentationIdeal Q ^ D := by
  apply ringHom_mem_ideal_power (groupRingMap f) (augmentationIdeal G) (augmentationIdeal Q) _ D x hx
  intro y hy
  change augmentation Q (groupRingMap f y) = 0
  rw [augmentation_groupRingMap]
  exact hy

/-- The actual functorial map on the augmentation quotients. -/
noncomputable def truncatedMap {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (D : ℕ) : TruncatedGroupRing G D →+* TruncatedGroupRing Q D :=
  Ideal.Quotient.lift (augmentationIdeal G ^ D) ((truncate Q D).comp (groupRingMap f))
    (fun x hx => (Ideal.Quotient.eq_zero_iff_mem).mpr (groupRingMap_augmentation_power f D x hx))

@[simp] theorem truncatedMap_element {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (D : ℕ) (g : G) :
    truncatedMap f D (truncatedElement G D g) = truncatedElement Q D (f g) := by
  change truncate Q D (groupRingMap f (MonoidAlgebra.of ℤ G g)) = _
  rw [groupRingMap_of]
  rfl

theorem groupRingMap_surjective {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) : Function.Surjective (groupRingMap f) := by
  intro x
  induction x using MonoidAlgebra.induction_on with
  | of q =>
    obtain ⟨g,rfl⟩ := hf q
    exact ⟨MonoidAlgebra.of ℤ G g,groupRingMap_of f g⟩
  | add x y hx hy =>
    obtain ⟨a,rfl⟩ := hx
    obtain ⟨b,rfl⟩ := hy
    exact ⟨a+b,map_add _ _ _⟩
  | smul z x hx =>
    obtain ⟨a,rfl⟩ := hx
    exact ⟨z • a,map_zsmul _ _ _⟩

theorem truncatedMap_surjective {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (D : ℕ) :
    Function.Surjective (truncatedMap f D) := by
  intro x
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b,rfl⟩ := groupRingMap_surjective f hf a
  exact ⟨truncate G D b,rfl⟩

end DirectedCycles
