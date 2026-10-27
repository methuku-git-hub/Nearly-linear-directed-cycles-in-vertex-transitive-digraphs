module

public import DirectedCycles.WeightedWordNorm
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- Right-invariant distance from a point to a finite nonempty set. The orientation
is chosen to control left translations by the norm of their translating element. -/
noncomputable def normSetDistance (d : G → ℝ) (A : Finset G) (hA : A.Nonempty) (x : G) : ℝ :=
  A.inf' hA (fun a => d (x*a⁻¹))

theorem normSetDistance_nonneg {d : G → ℝ} (hd : ∀ g, 0 ≤ d g)
    (A : Finset G) (hA : A.Nonempty) (x : G) : 0 ≤ normSetDistance d A hA x := by
  apply Finset.le_inf'
  intro a _
  exact hd _

theorem normSetDistance_le {d : G → ℝ} {A : Finset G} (hA : A.Nonempty)
    (x : G) {a : G} (ha : a ∈ A) : normSetDistance d A hA x ≤ d (x*a⁻¹) :=
  Finset.inf'_le _ ha

theorem normSetDistance_eq_zero {d : G → ℝ} (hd : ∀ g, 0 ≤ d g) (hd1 : d 1 = 0)
    {A : Finset G} (hA : A.Nonempty) {x : G} (hx : x ∈ A) :
    normSetDistance d A hA x = 0 := by
  apply le_antisymm _ (normSetDistance_nonneg hd A hA x)
  simpa [hd1] using normSetDistance_le (d := d) hA x hx

theorem normSetDistance_mul_le {d : G → ℝ}
    (hm : ∀ g h, d (g*h) ≤ d g + d h)
    (A : Finset G) (hA : A.Nonempty) (g x : G) :
    normSetDistance d A hA (g*x) ≤ d g + normSetDistance d A hA x := by
  apply (sub_le_iff_le_add').mp
  apply Finset.le_inf'
  intro a ha
  rw [sub_le_iff_le_add']
  exact (normSetDistance_le hA (g*x) ha).trans (by simpa [mul_assoc] using hm g (x*a⁻¹))

theorem normSetDistance_lipschitz {d : G → ℝ}
    (hm : ∀ g h, d (g*h) ≤ d g + d h) (hi : ∀ g, d g⁻¹ = d g)
    (A : Finset G) (hA : A.Nonempty) (g x : G) :
    |normSetDistance d A hA (g*x) - normSetDistance d A hA x| ≤ d g := by
  rw [abs_le]
  have h1 := normSetDistance_mul_le hm A hA g x
  have h2 := normSetDistance_mul_le hm A hA g⁻¹ (g*x)
  simp only [inv_mul_cancel_left, hi] at h2
  constructor <;> linarith

/-- Positive separation from the complement forces the distance to be large
outside the square. This is the support argument for the BGT bump. -/
theorem le_normSetDistance_of_not_mem_square {d : G → ℝ} {A : Finset G}
    (hA : A.Nonempty) {r : ℝ} (hsep : ∀ g : G, g ∉ A → r ≤ d g)
    {x : G} (hx : x ∉ (A : Set G)*(A : Set G)) : r ≤ normSetDistance d A hA x := by
  apply Finset.le_inf'
  intro a ha
  apply hsep
  intro hxa
  apply hx
  exact ⟨x*a⁻¹,hxa,a,ha,by simp⟩
end DirectedCycles
