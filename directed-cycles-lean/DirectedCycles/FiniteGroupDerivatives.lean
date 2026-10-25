module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G]

def leftShift (g : G) (f : G → ℝ) : G → ℝ := fun x => f (g⁻¹*x)
def groupDerivative (g : G) (f : G → ℝ) : G → ℝ := leftShift g f - f

@[simp] theorem leftShift_one (f : G → ℝ) : leftShift 1 f = f := by
  ext x
  simp [leftShift]

theorem leftShift_mul (g h : G) (f : G → ℝ) : leftShift (g*h) f = leftShift g (leftShift h f) := by
  ext x
  simp [leftShift, mul_assoc]

@[simp] theorem groupDerivative_one (f : G → ℝ) : groupDerivative 1 f = 0 := by
  simp [groupDerivative]

theorem groupDerivative_mul (g h : G) (f : G → ℝ) :
    groupDerivative (g*h) f = leftShift g (groupDerivative h f) + groupDerivative g f := by
  ext x
  simp only [groupDerivative, leftShift, mul_inv_rev, Pi.add_apply, Pi.sub_apply]
  simp only [mul_assoc]
  ring

/-- Exact discrete Taylor identity, before any norm estimate. -/
theorem groupDerivative_pow (g : G) (f : G → ℝ) (n : ℕ) (x : G) :
    groupDerivative (g^n) f x = (n : ℝ)*groupDerivative g f x +
      ∑ i ∈ Finset.range n, groupDerivative (g^i) (groupDerivative g f) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, groupDerivative_mul, Pi.add_apply, ih, Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one, groupDerivative, Pi.sub_apply]
    ring

section Finite
variable [Fintype G]

noncomputable def derivativeNorm (f : G → ℝ) (g : G) : ℝ := ‖groupDerivative g f‖

theorem norm_leftShift (g : G) (f : G → ℝ) : ‖leftShift g f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).2
    intro x
    exact norm_le_pi_norm f (g⁻¹*x)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (leftShift g f))).2
    intro x
    simpa [leftShift] using norm_le_pi_norm (leftShift g f) (g*x)

theorem abs_groupDerivative_le (f : G → ℝ) (g x : G) :
    |groupDerivative g f x| ≤ derivativeNorm f g := by
  simpa [Real.norm_eq_abs, derivativeNorm] using norm_le_pi_norm (groupDerivative g f) x

theorem derivativeNorm_le_iff (f : G → ℝ) (g : G) {r : ℝ} (hr : 0 ≤ r) :
    derivativeNorm f g ≤ r ↔ ∀ x, |groupDerivative g f x| ≤ r :=
  pi_norm_le_iff_of_nonneg hr

theorem derivativeNorm_nonneg (f : G → ℝ) (g : G) : 0 ≤ derivativeNorm f g := norm_nonneg _

@[simp] theorem derivativeNorm_one (f : G → ℝ) : derivativeNorm f 1 = 0 := by
  simp [derivativeNorm]

theorem derivativeNorm_mul_le (f : G → ℝ) (g h : G) :
    derivativeNorm f (g*h) ≤ derivativeNorm f g + derivativeNorm f h := by
  unfold derivativeNorm
  rw [groupDerivative_mul]
  exact (norm_add_le _ _).trans_eq (by rw [norm_leftShift, add_comm])

theorem derivativeNorm_inv (f : G → ℝ) (g : G) : derivativeNorm f g⁻¹ = derivativeNorm f g := by
  have he : groupDerivative g⁻¹ f = -leftShift g⁻¹ (groupDerivative g f) := by
    ext x
    simp [groupDerivative, leftShift]
  unfold derivativeNorm
  rw [he, norm_neg, norm_leftShift]

theorem derivativeNorm_le_two_mul (f : G → ℝ) (g : G) :
    derivativeNorm f g ≤ 2*‖f‖ := by
  unfold derivativeNorm groupDerivative
  exact (norm_sub_le _ _).trans_eq (by rw [norm_leftShift]; ring)

/-- A rigorous norm bound from the exact Taylor identity. -/
theorem derivativeNorm_taylor_bound (f : G → ℝ) (g : G) {n : ℕ} (hn : 0 < n) :
    derivativeNorm f g ≤ (2*‖f‖ +
      ∑ i ∈ Finset.range n, derivativeNorm (groupDerivative g f) (g^i)) / n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnum : 0 ≤ 2*‖f‖ + ∑ i ∈ Finset.range n,
      derivativeNorm (groupDerivative g f) (g^i) := add_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
      (Finset.sum_nonneg (fun i _ => derivativeNorm_nonneg _ _))
  apply (derivativeNorm_le_iff f g (div_nonneg hnum hnR.le)).2
  intro x
  rw [le_div_iff₀ hnR]
  have he := groupDerivative_pow g f n x
  have he' : (n : ℝ)*groupDerivative g f x = groupDerivative (g^n) f x -
      ∑ i ∈ Finset.range n, groupDerivative (g^i) (groupDerivative g f) x := by linarith
  calc
    |groupDerivative g f x| * (n : ℝ) = |(n : ℝ)*groupDerivative g f x| := by
      rw [abs_mul, abs_of_pos hnR, mul_comm]
    _ ≤ |groupDerivative (g^n) f x| +
        |∑ i ∈ Finset.range n, groupDerivative (g^i) (groupDerivative g f) x| := by
      rw [he']; exact abs_sub _ _
    _ ≤ derivativeNorm f (g^n) + ∑ i ∈ Finset.range n,
        derivativeNorm (groupDerivative g f) (g^i) := by
      apply add_le_add (abs_groupDerivative_le f (g^n) x)
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ => abs_groupDerivative_le _ (g^i) x))
    _ ≤ 2*‖f‖ + ∑ i ∈ Finset.range n,
        derivativeNorm (groupDerivative g f) (g^i) :=
      add_le_add (derivativeNorm_le_two_mul f (g^n)) le_rfl
omit [Fintype G] in
/-- The commutator identity with the explicit convention g⁻¹h⁻¹gh. -/
theorem groupDerivative_commutator_identity (g h : G) (f : G → ℝ) :
    leftShift (h*g) (groupDerivative (g⁻¹*h⁻¹*g*h) f) =
      groupDerivative g (groupDerivative h f) - groupDerivative h (groupDerivative g f) := by
  ext x
  simp [groupDerivative, leftShift, mul_assoc]
  ring

theorem derivativeNorm_commutator_le (f : G → ℝ) (g h : G) :
    derivativeNorm f (g⁻¹*h⁻¹*g*h) ≤
      derivativeNorm (groupDerivative h f) g + derivativeNorm (groupDerivative g f) h := by
  unfold derivativeNorm
  rw [← norm_leftShift (h*g), groupDerivative_commutator_identity]
  exact norm_sub_le _ _
end Finite
end DirectedCycles
