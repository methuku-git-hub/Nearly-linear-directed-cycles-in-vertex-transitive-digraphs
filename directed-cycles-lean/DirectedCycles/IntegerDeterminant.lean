import DirectedCycles.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- The adjugate identity applies to integer combinations in any abelian
group, including groups with torsion. -/
theorem integer_determinant_span {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] (A : Matrix ι ι ℤ) (v : ι → V) (W : AddSubgroup V)
    (h : ∀ i, ∑ j, A i j • v j ∈ W) : ∀ i, A.det • v i ∈ W := by
  intro i
  have hs : ∑ k, A.adjugate i k • (∑ j, A k j • v j) ∈ W :=
    W.sum_mem (fun k _ => W.zsmul_mem (h k) _)
  have he : (∑ k, A.adjugate i k • (∑ j, A k j • v j)) = A.det • v i := by
    simp only [Finset.smul_sum, ← mul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.adjugate_mul,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    simp
  rwa [he] at hs

/-- Taking the absolute value of the integer determinant preserves the
span inclusion and provides a positive multiplier when the determinant is nonzero. -/
theorem integer_abs_determinant_span {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] (A : Matrix ι ι ℤ) (v : ι → V) (W : AddSubgroup V)
    (h : ∀ i, ∑ j, A i j • v j ∈ W) : ∀ i, A.det.natAbs • v i ∈ W := by
  intro i
  have hd := integer_determinant_span A v W h i
  rcases le_total 0 A.det with hp | hn
  · have he : (A.det.natAbs : ℤ) = A.det := by rw [Int.natCast_natAbs, abs_of_nonneg hp]
    rw [← natCast_zsmul, he]
    exact hd
  · have he : (A.det.natAbs : ℤ) = -A.det := by rw [Int.natCast_natAbs, abs_of_nonpos hn]
    rw [← natCast_zsmul, he, neg_zsmul]
    exact W.neg_mem hd

/-- The factorial determinant bound used for the integer interpolation matrix. -/
theorem integer_determinant_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (B : ℕ) (h : ∀ i j, (A i j).natAbs ≤ B) :
    A.det.natAbs ≤ (Fintype.card ι).factorial * B ^ Fintype.card ι := by
  have hab : ∀ i j, |A i j| ≤ (B : ℤ) := by
    intro i j
    rw [← Int.natCast_natAbs]
    exact_mod_cast h i j
  have hd := Matrix.det_le (abv := AbsoluteValue.abs) hab
  simpa only [AbsoluteValue.abs_apply, nsmul_eq_mul, ← Int.natCast_natAbs,
    ← Nat.cast_pow, ← Nat.cast_mul, Int.ofNat_le] using hd

end DirectedCycles
