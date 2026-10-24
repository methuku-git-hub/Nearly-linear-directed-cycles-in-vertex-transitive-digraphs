import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

noncomputable def binomialVariable {n : ℕ} (i : Fin n) (k : ℕ) :
    MvPolynomial (Fin n) ℚ :=
  MvPolynomial.C ((k.factorial : ℚ)⁻¹) *
    ∏ j ∈ Finset.range k, (MvPolynomial.X i - MvPolynomial.C (j : ℚ))

noncomputable def binomialTensor {n : ℕ} (a : Fin n → ℕ) :
    MvPolynomial (Fin n) ℚ := ∏ i, binomialVariable i (a i)

theorem binomialVariable_eval {n : ℕ} (i : Fin n) (k : ℕ) (t : Fin n → ℕ) :
    MvPolynomial.eval (fun j => (t j : ℚ)) (binomialVariable i k) = (t i).choose k := by
  simp only [binomialVariable,map_mul,map_prod,map_sub,MvPolynomial.eval_X,MvPolynomial.eval_C]
  rw [← descPochhammer_eval_eq_prod_range, Nat.cast_choose_eq_descPochhammer_div]
  simpa only [div_eq_mul_inv] using mul_comm ((k.factorial : ℚ)⁻¹) ((descPochhammer ℚ k).eval (t i))

theorem binomialTensor_eval {n : ℕ} (a t : Fin n → ℕ) :
    MvPolynomial.eval (fun j => (t j : ℚ)) (binomialTensor a) =
      ∏ i, ((t i).choose (a i) : ℚ) := by
  simp only [binomialTensor,map_prod,binomialVariable_eval]

theorem binomialVariable_degree {n : ℕ} (i : Fin n) (k : ℕ) :
    (binomialVariable i k).totalDegree ≤ k := by
  unfold binomialVariable
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp only [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc
    ∑ j ∈ Finset.range k, (MvPolynomial.X i - MvPolynomial.C (j : ℚ)).totalDegree ≤
        ∑ _j ∈ Finset.range k, 1 := by
      apply Finset.sum_le_sum
      intro j _
      exact (MvPolynomial.totalDegree_sub_C_le _ _).trans (by simp)
    _ = k := by simp

theorem binomialTensor_degree {n : ℕ} (a : Fin n → ℕ) :
    (binomialTensor a).totalDegree ≤ ∑ i, a i := by
  exact (MvPolynomial.totalDegree_finsetProd _ _).trans
    (Finset.sum_le_sum fun i _ => binomialVariable_degree i (a i))

/-- The tensor binomial evaluation on its defining box is triangular with
unit diagonal; the coefficients are determined without a characteristic hypothesis. -/
theorem binomial_box_independent {n D : ℕ} {R : Type*} [CommRing R]
    (c : (Fin n → Fin D) → R)
    (h : ∀ a : Fin n → Fin D, ∑ b, (∏ i, ((a i).val.choose (b i).val : R)) * c b = 0) :
    c = 0 := by
  classical
  have hc : ∀ s : ℕ, ∀ a : Fin n → Fin D, (∑ i, (a i).val) = s → c a = 0 := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro a ha
      have ht : ∀ b : Fin n → Fin D, b ≠ a →
          (∏ i, ((a i).val.choose (b i).val : R)) * c b = 0 := by
        intro b hba
        by_cases hle : ∀ i, (b i).val ≤ (a i).val
        · have hne : ∃ i, (b i).val < (a i).val := by
            by_contra hh
            push Not at hh
            apply hba
            funext i
            exact Fin.ext (Nat.le_antisymm (hle i) (hh i))
          have hsum : (∑ i, (b i).val) < s := by
            rw [← ha]
            exact Finset.sum_lt_sum (fun i _ => hle i)
              (hne.elim fun i hi => ⟨i,Finset.mem_univ _,hi⟩)
          rw [ih _ hsum b rfl,mul_zero]
        · push Not at hle
          obtain ⟨i,hi⟩ := hle
          have hz : (∏ j, ((a j).val.choose (b j).val : R)) = 0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ i)
            rw [Nat.choose_eq_zero_of_lt hi,Nat.cast_zero]
          rw [hz,zero_mul]
      have he := h a
      rw [Finset.sum_eq_single a] at he
      · simpa using he
      · intro b _ hba
        exact ht b hba
      · simp
  funext a
  exact hc _ a rfl

end DirectedCycles
