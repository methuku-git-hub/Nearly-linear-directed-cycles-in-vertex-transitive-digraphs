module

public import DirectedCycles.WeightedWordNorm
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- Right-invariant distance to an arbitrary nonempty set for a
nonnegative subadditive group gauge. -/
noncomputable def openSetNormDistance (d : G → ℝ) (A : Set G) (x : G) : ℝ :=
  sInf ((fun a => d (x*a⁻¹)) '' A)

theorem openSetNormDistance_values_nonempty (d : G → ℝ) {A : Set G}
    (hA : A.Nonempty) (x : G) : ((fun a => d (x*a⁻¹)) '' A).Nonempty := hA.image _

theorem openSetNormDistance_values_bddBelow {d : G → ℝ} (hd : ∀ g, 0 ≤ d g)
    (A : Set G) (x : G) : BddBelow ((fun a => d (x*a⁻¹)) '' A) :=
  ⟨0,by rintro _ ⟨a,_ha,rfl⟩; exact hd _⟩

theorem openSetNormDistance_nonneg {d : G → ℝ} (hd : ∀ g, 0 ≤ d g)
    {A : Set G} (hA : A.Nonempty) (x : G) : 0 ≤ openSetNormDistance d A x := by
  apply le_csInf (openSetNormDistance_values_nonempty d hA x)
  rintro _ ⟨a,_ha,rfl⟩
  exact hd _

theorem openSetNormDistance_le {d : G → ℝ} (hd : ∀ g, 0 ≤ d g)
    {A : Set G} (x : G) {a : G} (ha : a ∈ A) : openSetNormDistance d A x ≤ d (x*a⁻¹) :=
  csInf_le (openSetNormDistance_values_bddBelow hd A x) ⟨a,ha,rfl⟩

theorem openSetNormDistance_eq_zero {d : G → ℝ} (hd : ∀ g, 0 ≤ d g) (hd1 : d 1 = 0)
    {A : Set G} {x : G} (hx : x ∈ A) : openSetNormDistance d A x = 0 := by
  apply le_antisymm _ (openSetNormDistance_nonneg hd ⟨x,hx⟩ x)
  simpa [hd1] using openSetNormDistance_le hd x hx

theorem openSetNormDistance_mul_le {d : G → ℝ} (hd : ∀ g, 0 ≤ d g)
    (hm : ∀ g h, d (g*h) ≤ d g+d h) {A : Set G} (hA : A.Nonempty) (g x : G) :
    openSetNormDistance d A (g*x) ≤ d g+openSetNormDistance d A x := by
  apply (sub_le_iff_le_add').mp
  apply le_csInf (openSetNormDistance_values_nonempty d hA x)
  rintro _ ⟨a,ha,rfl⟩
  rw [sub_le_iff_le_add']
  exact (openSetNormDistance_le hd (g*x) ha).trans (by simpa [mul_assoc] using hm g (x*a⁻¹))

theorem openSetNormDistance_lipschitz {d : G → ℝ} (hd : ∀ g, 0 ≤ d g)
    (hm : ∀ g h, d (g*h) ≤ d g+d h) (hi : ∀ g, d g⁻¹ = d g)
    {A : Set G} (hA : A.Nonempty) (g x : G) :
    |openSetNormDistance d A (g*x)-openSetNormDistance d A x| ≤ d g := by
  rw [abs_le]
  have h1 := openSetNormDistance_mul_le hd hm hA g x
  have h2 := openSetNormDistance_mul_le hd hm hA g⁻¹ (g*x)
  simp only [inv_mul_cancel_left,hi] at h2
  constructor <;> linarith

theorem le_openSetNormDistance_outside_square {d : G → ℝ} {A : Set G}
    (hA : A.Nonempty) {r : ℝ} (hsep : ∀ g : G, g ∉ A → r ≤ d g)
    {x : G} (hx : x ∉ A*A) : r ≤ openSetNormDistance d A x := by
  apply le_csInf (openSetNormDistance_values_nonempty d hA x)
  rintro _ ⟨a,ha,rfl⟩
  apply hsep
  intro hxa
  exact hx ⟨x*a⁻¹,hxa,a,ha,by simp⟩

/-- Sublevel sets are products with the original open set. This proves
measurability even for a regularized gauge that is discontinuous at one. -/
theorem openSetNormDistance_sublevel {d : G → ℝ} (hd : ∀ g, 0 ≤ d g)
    {A : Set G} (hA : A.Nonempty) (t : ℝ) :
    {x | openSetNormDistance d A x < t} = {x | d x < t}*A := by
  ext x
  constructor
  · intro hx
    obtain ⟨c,⟨a,ha,rfl⟩,hc⟩ := (csInf_lt_iff
      (openSetNormDistance_values_bddBelow hd A x)
      (openSetNormDistance_values_nonempty d hA x)).mp hx
    exact ⟨x*a⁻¹,hc,a,ha,by simp⟩
  · rintro ⟨g,hg,a,ha,rfl⟩
    exact (openSetNormDistance_le hd (g*a) ha).trans_lt (by simpa using hg)

theorem openSetNormDistance_measurable [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [OpensMeasurableSpace G] {d : G → ℝ} (hd : ∀ g, 0 ≤ d g)
    {A : Set G} (hA : A.Nonempty) (hAo : IsOpen A) : Measurable (openSetNormDistance d A) := by
  apply measurable_of_Iio
  intro t
  change MeasurableSet {x | openSetNormDistance d A x < t}
  rw [openSetNormDistance_sublevel hd hA]
  exact hAo.mul_left.measurableSet
end DirectedCycles
