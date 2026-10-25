module

public import DirectedCycles.OpenSetNormDistance
public import Mathlib.Algebra.Order.Group.MinMax

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- The actual bounded bump on an arbitrary open set. -/
noncomputable def openSetNormBump (d : G → ℝ) (A : Set G) (r : ℝ) (x : G) : ℝ :=
  max (1-openSetNormDistance d A x/r) 0

theorem openSetNormBump_bounds {d : G → ℝ} (hd : ∀ g, 0 ≤ d g)
    {A : Set G} (hA : A.Nonempty) {r : ℝ} (hr : 0 ≤ r) (x : G) :
    0 ≤ openSetNormBump d A r x ∧ openSetNormBump d A r x ≤ 1 := by
  refine ⟨le_max_right _ _,max_le ?_ zero_le_one⟩
  have := div_nonneg (openSetNormDistance_nonneg hd hA x) hr
  linarith

theorem openSetNormBump_plateau {d : G → ℝ} (hd : ∀ g, 0 ≤ d g) (hd1 : d 1 = 0)
    {A : Set G} (r : ℝ) {x : G} (hx : x ∈ A) : openSetNormBump d A r x = 1 := by
  simp [openSetNormBump,openSetNormDistance_eq_zero hd hd1 hx]

theorem openSetNormBump_support {d : G → ℝ} {A : Set G} (hA : A.Nonempty)
    {r : ℝ} (hr : 0 < r) (hsep : ∀ g : G, g ∉ A → r ≤ d g)
    {x : G} (hx : x ∉ A^2) : openSetNormBump d A r x = 0 := by
  apply max_eq_right
  have hh := le_openSetNormDistance_outside_square hA hsep (by simpa only [pow_two] using hx)
  have hh' : 1 ≤ openSetNormDistance d A x/r := (le_div_iff₀ hr).2 (by simpa using hh)
  linarith

theorem openSetNormBump_lipschitz {d : G → ℝ} (hd : ∀ g, 0 ≤ d g)
    (hm : ∀ g h, d (g*h) ≤ d g+d h) (hi : ∀ g, d g⁻¹ = d g)
    {A : Set G} (hA : A.Nonempty) {r : ℝ} (hr : 0 < r) (g x : G) :
    |openSetNormBump d A r (g*x)-openSetNormBump d A r x| ≤ d g/r := by
  unfold openSetNormBump
  apply (abs_max_sub_max_le_abs _ _ 0).trans
  have he : (1-openSetNormDistance d A (g*x)/r)-(1-openSetNormDistance d A x/r) =
      -(openSetNormDistance d A (g*x)-openSetNormDistance d A x)/r := by ring
  rw [he,abs_div,abs_neg,abs_of_pos hr]
  exact div_le_div_of_nonneg_right (openSetNormDistance_lipschitz hd hm hi hA g x) hr.le

theorem openSetNormBump_measurable [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [OpensMeasurableSpace G] {d : G → ℝ} (hd : ∀ g, 0 ≤ d g)
    {A : Set G} (hA : A.Nonempty) (hAo : IsOpen A) (r : ℝ) :
    Measurable (openSetNormBump d A r) :=
  (measurable_const.sub ((openSetNormDistance_measurable hd hA hAo).div_const r)).max measurable_const
end DirectedCycles
