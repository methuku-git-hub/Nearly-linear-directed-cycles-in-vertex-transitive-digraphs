module

public import DirectedCycles.GleasonMetricTopology
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The elementary rounding error for the difference of two real floors. -/
theorem abs_floor_sub_floor_le (a b : ℝ) :
    |((Int.floor a-Int.floor b : ℤ) : ℝ)| ≤ |a-b|+1 := by
  have ha₁ := Int.floor_le a
  have ha₂ := Int.lt_floor_add_one a
  have hb₁ := Int.floor_le b
  have hb₂ := Int.lt_floor_add_one b
  rw [Int.cast_sub]
  apply abs_le.mpr
  constructor <;> linarith [neg_abs_le (a-b),le_abs_self (a-b)]

/-- Integer powers at a rounded real proportion of a natural scale. -/
noncomputable def roundedPower {G : Type*} [Group G] (g : G) (N : ℕ) (t : ℝ) : G :=
  g^(Int.floor (t*(N : ℝ)))

@[simp] theorem roundedPower_zero {G : Type*} [Group G] (g : G) (N : ℕ) :
    roundedPower g N 0 = 1 := by simp [roundedPower]

@[simp] theorem roundedPower_one {G : Type*} [Group G] (g : G) (N : ℕ) :
    roundedPower g N 1 = g^N := by simp [roundedPower]

namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

theorem dist_zpow_eq (g : G) (a b : ℤ) :
    D.metric.dist (g^a) (g^b) = D.gauge (g^(b-a)) := by
  rw [D.dist_eq_gauge,← zpow_neg,← zpow_add]
  congr 2
  omega

/-- The rounded powers have a linear modulus with one generator-sized
rounding error. -/
theorem roundedPower_distance (g : G) (N : ℕ) (s t : ℝ) :
    D.metric.dist (roundedPower g N s) (roundedPower g N t) ≤
      ((N : ℝ)*|t-s|+1)*D.gauge g := by
  rw [roundedPower,roundedPower,D.dist_zpow_eq]
  have hfloor := abs_floor_sub_floor_le (t*(N : ℝ)) (s*(N : ℝ))
  have hid : |t*(N : ℝ)-s*(N : ℝ)| = (N : ℝ)*|t-s| := by
    rw [← sub_mul,abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ N from Nat.cast_nonneg N),mul_comm]
  rw [hid] at hfloor
  apply (D.gauge_zpow_le g _).trans
  apply mul_le_mul_of_nonneg_right ?_ (D.gauge_nonneg g)
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hfloor

theorem roundedPower_gauge (g : G) (N : ℕ) (t : ℝ) :
    D.gauge (roundedPower g N t) ≤ ((N : ℝ)*|t|+1)*D.gauge g := by
  simpa only [roundedPower_zero,sub_zero,gauge] using D.roundedPower_distance g N 0 t

/-- The addition error is either zero or exactly one extra generator. -/
theorem roundedPower_add_defect (g : G) (N : ℕ) (s t : ℝ) :
    D.metric.dist (roundedPower g N (s+t)) (roundedPower g N s*roundedPower g N t) ≤ D.gauge g := by
  have h₁ := Int.le_floor_add (s*(N : ℝ)) (t*(N : ℝ))
  have h₂ := Int.le_floor_add_floor (s*(N : ℝ)) (t*(N : ℝ))
  rw [← add_mul] at h₁ h₂
  have he : Int.floor ((s+t)*(N : ℝ)) = Int.floor (s*(N : ℝ))+Int.floor (t*(N : ℝ)) ∨
      Int.floor ((s+t)*(N : ℝ)) = Int.floor (s*(N : ℝ))+Int.floor (t*(N : ℝ))+1 := by omega
  rcases he with he | he
  · simp only [roundedPower,he,zpow_add,D.metric.dist_self]
    exact D.gauge_nonneg g
  · simp only [roundedPower,he,zpow_add,zpow_one]
    have hd := D.left_invariant (g^⌊s*(N : ℝ)⌋*g^⌊t*(N : ℝ)⌋) g 1
    simp only [mul_one] at hd
    rw [hd,D.metric.dist_comm]
    rfl
end GleasonMetricData
end DirectedCycles
