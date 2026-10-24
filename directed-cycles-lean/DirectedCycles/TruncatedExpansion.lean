import DirectedCycles.TruncatedPowers
import DirectedCycles.PowerCoordinates
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- The ordinary nonnegative binomial expansion truncated by actual
nilpotence, valid in a noncommutative ring. -/
theorem nilpotent_binomial_expansion {R : Type*} [Ring R] (x : R) (D t : ℕ)
    (hD : (x-1)^D = 0) :
    x^t = ∑ j : Fin D, (t.choose j.val : ℤ) • (x-1)^j.val := by
  have he := (Commute.one_right (x-1)).add_pow t
  simp only [sub_add_cancel,one_pow,mul_one] at he
  have hr : (∑ j ∈ Finset.range (t+1), (x-1)^j * (t.choose j : R)) =
      ∑ j ∈ Finset.range D, (x-1)^j * (t.choose j : R) := by
    rcases le_total (t+1) D with hle | hle
    · apply Finset.sum_subset (Finset.range_mono hle)
      intro j _ hj
      have hj' : t < j := by simpa using hj
      rw [Nat.choose_eq_zero_of_lt hj',Nat.cast_zero,mul_zero]
    · symm
      apply Finset.sum_subset (Finset.range_mono hle)
      intro j _ hj
      have hj' : D ≤ j := by simpa using hj
      rw [pow_eq_zero_of_le hj' hD,zero_mul]
  rw [he,hr,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [natCast_zsmul,nsmul_eq_mul']

/-- Expansion of an ordered product of finite sums without commuting
any factors of the target ring. -/
theorem ordered_sum_product {R : Type*} [Ring R] {n D : ℕ}
    (c : Fin n → Fin D → ℤ) (v : Fin n → Fin D → R) :
    (List.ofFn (fun i => ∑ j, c i j • v i j)).prod =
      ∑ a : Fin n → Fin D, (∏ i, c i (a i)) • (List.ofFn (fun i => v i (a i))).prod := by
  let f := MultilinearMap.mkPiAlgebraFin ℤ n R
  have h := f.map_sum (fun i j => c i j • v i j)
  simp only [MultilinearMap.map_smul_univ] at h
  exact h

/-- The ordered binomial coefficients of a coordinate system in the
truncated integral group ring. -/
noncomputable def truncatedCoordinateCoefficient {G : Type*} [Group G]
    (D : ℕ) {n : ℕ} (u : Fin n → G) (z : G) (a : Fin n → Fin D) :
    TruncatedGroupRing G D :=
  truncatedElement G D z *
    (List.ofFn (fun i => (truncatedElement G D (u i)-1)^(a i).val)).prod

theorem truncated_nat_coordinates_expansion {G : Type*} [Group G]
    (D : ℕ) {n : ℕ} (u : Fin n → G) (z : G) (t : Fin n → ℕ) :
    truncatedElement G D (z * powerWord u (fun i => (t i : ℤ))) =
      ∑ a : Fin n → Fin D, (∏ i, ((t i).choose (a i).val : ℤ)) •
        truncatedCoordinateCoefficient D u z a := by
  rw [map_mul]
  have he : truncatedElement G D (powerWord u (fun i => (t i : ℤ))) =
      (List.ofFn (fun i => ∑ j : Fin D, ((t i).choose j.val : ℤ) •
        (truncatedElement G D (u i)-1)^j.val)).prod := by
    simp only [powerWord, map_list_prod, List.map_ofFn, Function.comp_def, zpow_natCast, map_pow]
    congr 2
    funext i
    exact nilpotent_binomial_expansion _ D (t i) (truncated_difference_pow D (u i))
  rw [he,ordered_sum_product,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_smul_comm _ _ _

/-- In a finite group, integer power coordinates can be chosen nonnegative. -/
theorem powerWord_nat_surjective {G : Type*} [Group G] [Finite G]
    {n : ℕ} (u : Fin n → G) (hu : Function.Surjective (powerWord u)) :
    Function.Surjective (fun t : Fin n → ℕ => powerWord u (fun i => (t i : ℤ))) := by
  intro g
  obtain ⟨a,ha⟩ := hu g
  have h : ∀ i, ∃ t : ℕ, (u i)^t = (u i)^(a i) := by
    intro i
    have hm : (u i)^(a i) ∈ Subgroup.zpowers (u i) := Subgroup.zpow_mem_zpowers _ _
    exact mem_powers_iff_mem_zpowers.mpr hm
  choose t ht using h
  refine ⟨t,?_⟩
  change powerWord u (fun i => (t i : ℤ)) = g
  rw [← ha]
  apply congrArg (fun w : Fin n → G => (List.ofFn w).prod)
  funext i
  simpa only [zpow_natCast] using ht i

/-- A uniform multiplier on the group-element generators holds on the
whole truncated group ring. -/
theorem truncated_multiplier_of_generators {G : Type*} [Group G] (D M : ℕ)
    (W : AddSubgroup (TruncatedGroupRing G D))
    (h : ∀ g, M • truncatedElement G D g ∈ W) :
    ∀ x, M • x ∈ W := by
  intro x
  have hx : x ∈ AddSubgroup.closure (Set.range (truncatedElement G D)) := by
    rw [truncated_elements_generate]
    trivial
  induction hx using AddSubgroup.closure_induction with
  | mem x hx => obtain ⟨g,rfl⟩ := hx; exact h g
  | zero => simpa only [smul_zero] using W.zero_mem
  | add x y _ _ hx hy => simpa only [nsmul_add] using W.add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact W.neg_mem hx

/-- Multiplied coordinate coefficients control the entire truncated group
ring once the ordered power coordinates cover the finite group. -/
theorem truncated_multiplier_of_coefficients {G : Type*} [Group G] [Finite G]
    (D M : ℕ) {n : ℕ} (u : Fin n → G) (hu : Function.Surjective (powerWord u))
    (z : G) (W : AddSubgroup (TruncatedGroupRing G D))
    (h : ∀ a, M • truncatedCoordinateCoefficient D u z a ∈ W) :
    ∀ x, M • x ∈ W := by
  apply truncated_multiplier_of_generators
  intro g
  obtain ⟨t,ht⟩ := powerWord_nat_surjective u hu (z⁻¹*g)
  change powerWord u (fun i => (t i : ℤ)) = z⁻¹*g at ht
  have hg : z * powerWord u (fun i => (t i : ℤ)) = g := by rw [ht,mul_inv_cancel_left]
  rw [← hg,truncated_nat_coordinates_expansion,Finset.smul_sum]
  apply W.sum_mem
  intro a _
  rw [smul_comm]
  exact W.zsmul_mem (h a) _

end DirectedCycles
