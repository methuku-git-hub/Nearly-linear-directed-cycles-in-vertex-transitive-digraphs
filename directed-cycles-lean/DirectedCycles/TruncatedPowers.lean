module

public import DirectedCycles.Augmentation
public import DirectedCycles.UnipotentRecurrence

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Left multiplication by a group element is an integral linear equivalence
of the actual truncated group ring. -/
noncomputable def truncatedLeftTranslation {G : Type*} [Group G] (D : ℕ) (g : G) :
    TruncatedGroupRing G D ≃ₗ[ℤ] TruncatedGroupRing G D where
  toFun x := truncatedElement G D g * x
  invFun x := truncatedElement G D g⁻¹ * x
  left_inv x := by
    change truncatedElement G D g⁻¹ * (truncatedElement G D g * x) = x
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  right_inv x := by
    change truncatedElement G D g * (truncatedElement G D g⁻¹ * x) = x
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  map_add' x y := mul_add _ x y
  map_smul' z x := mul_smul_comm z _ x

noncomputable def truncatedTranslationHom {G : Type*} [Group G] (D : ℕ) :
    G →* (TruncatedGroupRing G D ≃ₗ[ℤ] TruncatedGroupRing G D) where
  toFun := truncatedLeftTranslation D
  map_one' := LinearEquiv.ext (fun x => by change truncatedElement G D 1 * x = x; rw [map_one,one_mul])
  map_mul' g h := LinearEquiv.ext (fun x => by
    change truncatedElement G D (g*h) * x = truncatedElement G D g * (truncatedElement G D h * x)
    rw [map_mul,mul_assoc])

theorem truncatedLeftTranslation_zpow {G : Type*} [Group G] (D : ℕ) (g : G) (k : ℤ)
    (x : TruncatedGroupRing G D) :
    (truncatedLeftTranslation D g ^ k) x = truncatedElement G D (g ^ k) * x := by
  have h := map_zpow (truncatedTranslationHom (G := G) D) g k
  exact congrArg (fun L : TruncatedGroupRing G D ≃ₗ[ℤ] TruncatedGroupRing G D => L x) h.symm

/-- The left translation really is unipotent of the required order. -/
theorem truncatedLeftTranslation_unipotent {G : Type*} [Group G] (D : ℕ) (g : G) :
    ((truncatedLeftTranslation D g).toLinearMap - 1) ^ D = 0 := by
  have hp : ∀ n : ℕ, ∀ x : TruncatedGroupRing G D,
      (((truncatedLeftTranslation D g).toLinearMap - 1) ^ n) x =
        (truncatedElement G D g - 1) ^ n * x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, ih]
      change truncatedElement G D g * ((truncatedElement G D g - 1)^n*x) -
        ((truncatedElement G D g - 1)^n*x) = (truncatedElement G D g - 1)^(n+1)*x
      rw [pow_succ', mul_assoc, sub_mul, one_mul]
  apply LinearMap.ext
  intro x
  rw [hp, truncated_difference_pow, zero_mul]
  rfl

/-- The manuscript's consecutive-powers spanning property in Z[G]/I^D. -/
theorem truncated_consecutive_powers_mem {G : Type*} [Group G] (D : ℕ) (g : G)
    (W : AddSubgroup (TruncatedGroupRing G D)) (m : ℤ)
    (h : ∀ i : ℕ, i < D → truncatedElement G D (g ^ (m+i)) ∈ W) :
    ∀ k : ℤ, truncatedElement G D (g ^ k) ∈ W := by
  have hfirst : ∀ i : ℕ, i < D →
      (truncatedLeftTranslation D g ^ (m+i)) (1 : TruncatedGroupRing G D) ∈ W := by
    intro i hi
    rw [truncatedLeftTranslation_zpow, mul_one]
    exact h i hi
  intro k
  have hk := unipotent_consecutive_orbit_mem (truncatedLeftTranslation D g) W D
    (truncatedLeftTranslation_unipotent D g) 1 m hfirst k
  rwa [truncatedLeftTranslation_zpow, mul_one] at hk

end DirectedCycles
