module

public import DirectedCycles.NormSetDistance
public import Mathlib.Algebra.Order.Group.MinMax

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

noncomputable def normSetBump (d : G → ℝ) (A : Finset G) (hA : A.Nonempty)
    (r : ℝ) (x : G) : ℝ := max (1 - normSetDistance d A hA x / r) 0

theorem normSetBump_nonneg (d : G → ℝ) (A : Finset G) (hA : A.Nonempty)
    (r : ℝ) (x : G) : 0 ≤ normSetBump d A hA r x := le_max_right _ _

theorem normSetBump_le_one {d : G → ℝ} (hd : ∀ g, 0 ≤ d g)
    (A : Finset G) (hA : A.Nonempty) {r : ℝ} (hr : 0 ≤ r) (x : G) :
    normSetBump d A hA r x ≤ 1 := by
  apply max_le _ zero_le_one
  have := div_nonneg (normSetDistance_nonneg hd A hA x) hr
  linarith

theorem normSetBump_eq_one {d : G → ℝ} (hd : ∀ g, 0 ≤ d g) (hd1 : d 1 = 0)
    {A : Finset G} (hA : A.Nonempty) (r : ℝ) {x : G} (hx : x ∈ A) :
    normSetBump d A hA r x = 1 := by
  simp [normSetBump, normSetDistance_eq_zero hd hd1 hA hx]

theorem normSetBump_eq_zero {d : G → ℝ} {A : Finset G} (hA : A.Nonempty)
    {r : ℝ} (hr : 0 < r) (hsep : ∀ g : G, g ∉ A → r ≤ d g)
    {x : G} (hx : x ∉ (A : Set G)*(A : Set G)) :
    normSetBump d A hA r x = 0 := by
  apply max_eq_right
  have hh := le_normSetDistance_of_not_mem_square hA hsep hx
  have hh' : 1 ≤ normSetDistance d A hA x / r := (le_div_iff₀ hr).2 (by simpa using hh)
  linarith

theorem normSetBump_lipschitz {d : G → ℝ}
    (hm : ∀ g h, d (g*h) ≤ d g + d h) (hi : ∀ g, d g⁻¹ = d g)
    (A : Finset G) (hA : A.Nonempty) {r : ℝ} (hr : 0 < r) (g x : G) :
    |normSetBump d A hA r (g*x) - normSetBump d A hA r x| ≤ d g / r := by
  unfold normSetBump
  apply (abs_max_sub_max_le_abs _ _ 0).trans
  have he : (1-normSetDistance d A hA (g*x)/r) - (1-normSetDistance d A hA x/r) =
      -(normSetDistance d A hA (g*x)-normSetDistance d A hA x)/r := by ring
  rw [he, abs_div, abs_neg, abs_of_pos hr]
  exact div_le_div_of_nonneg_right (normSetDistance_lipschitz hm hi A hA g x) hr.le

/-- A finite-group form of the first BGT bump lemma with an explicit separation
radius, so that no infimum over a possibly empty complement is needed. -/
theorem exists_norm_bump {d : G → ℝ} (hd : ∀ g, 0 ≤ d g) (hd1 : d 1 = 0)
    (hm : ∀ g h, d (g*h) ≤ d g + d h) (hi : ∀ g, d g⁻¹ = d g)
    (A : Finset G) (hA : A.Nonempty) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ g : G, g ∉ A → r ≤ d g) :
    ∃ φ : G → ℝ, (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ x ∈ A, φ x = 1) ∧
      (∀ x, x ∉ (A : Set G)^2 → φ x = 0) ∧
      (∀ g x, |φ (g⁻¹*x)-φ x| ≤ d g/r) := by
  refine ⟨normSetBump d A hA r, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨normSetBump_nonneg .., normSetBump_le_one hd A hA hr.le x⟩
  · intro x hx
    exact normSetBump_eq_one hd hd1 hA r hx
  · intro x hx
    apply normSetBump_eq_zero hA hr hsep
    simpa [pow_two] using hx
  · intro g x
    simpa [hi] using normSetBump_lipschitz hm hi A hA hr g⁻¹ x
end DirectedCycles
