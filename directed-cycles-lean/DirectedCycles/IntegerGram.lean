import DirectedCycles.IntegerDeterminant
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
open scoped BigOperators Matrix
namespace DirectedCycles

/-- Injective rational evaluation gives a nonzero integer Gram determinant. -/
theorem integer_gram_det_ne_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (A : Matrix κ ι ℤ)
    (h : Function.Injective (A.map (Int.castRingHom ℚ)).mulVec) :
    (A.transpose * A).det ≠ 0 := by
  let Q := A.map (Int.castRingHom ℚ)
  have hker : LinearMap.ker (Q.transpose * Q).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot.mpr h
  have hinj : Function.Injective (Q.transpose * Q).mulVec :=
    LinearMap.ker_eq_bot.mp hker
  have hunit := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : (Q.transpose * Q).det ≠ 0 := (hunit.map Matrix.detMonoidHom).ne_zero
  intro hz
  apply hdet
  have he : (Q.transpose * Q).det = ((A.transpose * A).det : ℚ) := by
    have hm : Q.transpose * Q = (A.transpose * A).map (Int.castRingHom ℚ) := by
      ext i j
      simp [Q, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [hm]
    exact ((Int.castRingHom ℚ).map_det _).symm
  rw [he,hz,Int.cast_zero]

/-- The Gram rows are integer combinations of the original evaluations. -/
theorem integer_gram_span {ι κ V : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [AddCommGroup V] (A : Matrix κ ι ℤ)
    (v : ι → V) (W : AddSubgroup V)
    (h : ∀ k, ∑ j, A k j • v j ∈ W) :
    ∀ i, (A.transpose * A).det.natAbs • v i ∈ W := by
  apply integer_abs_determinant_span
  intro i
  have hs := W.sum_mem (t := Finset.univ) (fun k _ => W.zsmul_mem (h k) (A k i))
  convert hs using 1
  simp only [Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, Matrix.mul_apply, Matrix.transpose_apply]

/-- A rectangular integer evaluation matrix produces a bounded positive
multiplier for all coefficients in any abelian group, including torsion. -/
theorem integer_gram_multiplier {ι κ V : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [AddCommGroup V] (A : Matrix κ ι ℤ)
    (hinj : Function.Injective (A.map (Int.castRingHom ℚ)).mulVec)
    (B : ℕ) (hB : ∀ k i, (A k i).natAbs ≤ B)
    (v : ι → V) (W : AddSubgroup V)
    (h : ∀ k, ∑ j, A k j • v j ∈ W) :
    ∃ M : ℕ, 0 < M ∧
      M ≤ (Fintype.card ι).factorial * (Fintype.card κ * B^2)^Fintype.card ι ∧
      ∀ i, M • v i ∈ W := by
  refine ⟨(A.transpose * A).det.natAbs, ?_, ?_, integer_gram_span A v W h⟩
  · exact Int.natAbs_pos.mpr (integer_gram_det_ne_zero A hinj)
  · apply integer_determinant_bound
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    calc
      (∑ k, A k i * A k j).natAbs ≤ ∑ k, (A k i * A k j).natAbs :=
        Int.natAbs_sum_le _ _
      _ ≤ ∑ _ : κ, B^2 := by
        apply Finset.sum_le_sum
        intro k _
        rw [Int.natAbs_mul,pow_two]
        exact Nat.mul_le_mul (hB k i) (hB k j)
      _ = Fintype.card κ * B^2 := by simp

end DirectedCycles
