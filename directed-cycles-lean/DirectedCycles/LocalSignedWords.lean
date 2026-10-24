import DirectedCycles.LocalBoundedCostProducts
import DirectedCycles.LocalEscapeMaps
import Mathlib.Data.List.Count
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- The actual local-group letters of a signed word. -/
def signedLetters {r : ℕ} (g : Fin r → G) (w : List (Fin r × Bool)) : List G :=
  w.map (fun a => if a.2 then g a.1 else L.inv (g a.1))

/-- The noncommutative progression consists of actual all-bracketings word
products with bounded occurrences of each generator, allowing either sign. -/
def wordProgression {r : ℕ} (g : Fin r → G) (N : Fin r → ℕ) : Set G :=
  {x | ∃ w : List (Fin r × Bool), (∀ i, w.countP (fun a => a.1 = i) ≤ N i) ∧
    L.Product (L.signedLetters g w) x}

theorem signedLetters_escape_sum (hr : L.Reversible) {A : Set G}
    (hi : ∀ x ∈ A, L.inv x ∈ A) {r : ℕ} (g : Fin r → G) (w : List (Fin r × Bool)) :
    ((L.signedLetters g w).map (L.escapeNorm A)).sum =
      ∑ i : Fin r, (w.countP (fun a => a.1 = i) : ℝ)*L.escapeNorm A (g i) := by
  induction w with
  | nil => simp [signedLetters]
  | cons a w ih =>
    have hletter : L.escapeNorm A (if a.2 then g a.1 else L.inv (g a.1)) = L.escapeNorm A (g a.1) := by
      split
      · rfl
      · exact L.escapeNorm_inv hr hi _
    simp only [signedLetters,List.map_cons,List.sum_cons] at ih ⊢
    rw [hletter,ih]
    simp only [List.countP_cons]
    simp [Nat.cast_add,add_mul,Finset.sum_add_distrib,ite_mul,eq_comm,add_comm]

theorem signedLetters_escape_sum_le (hr : L.Reversible) {A : Set G}
    (hA : L.one ∈ A) (hi : ∀ x ∈ A, L.inv x ∈ A)
    {r : ℕ} (g : Fin r → G) (N : Fin r → ℕ) (w : List (Fin r × Bool))
    (hw : ∀ i, w.countP (fun a => a.1 = i) ≤ N i) :
    ((L.signedLetters g w).map (L.escapeNorm A)).sum ≤
      ∑ i : Fin r, (N i : ℝ)*L.escapeNorm A (g i) := by
  rw [L.signedLetters_escape_sum hr hi]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hw i) (L.escapeNorm_nonneg hA _)
end LocalGroupAlgebra

/-- All signed words in a sufficiently small progression exist, with every
bracketing, and lie in the finite strong source. -/
theorem strong_local_wordProgression_defined {G : Type*} [Fintype G]
    (L : LocalGroupAlgebra G) (hd : L.DivisionClosed) (hr : L.Reversible)
    {K : ℕ} {A : Finset G} (hA : IsStrongLocalFiniteApproximateGroup L K A)
    {r : ℕ} (g : Fin r → G) (N : Fin r → ℕ)
    (hsmall : (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)) *
      (∑ i : Fin r, (N i : ℝ)*L.escapeNorm A (g i)) < 1) :
    (∀ w : List (Fin r × Bool), (∀ i, w.countP (fun a => a.1 = i) ≤ N i) →
      ∃ x ∈ A, L.Product (L.signedLetters g w) x) ∧ L.wordProgression g N ⊆ A := by
  have hall : ∀ w : List (Fin r × Bool), (∀ i, w.countP (fun a => a.1 = i) ≤ N i) →
      ∃ x ∈ A, L.Product (L.signedLetters g w) x := by
    intro w hw
    obtain ⟨x,hx,hp,_⟩ := strong_local_small_word_exists L hd hr hA (L.signedLetters g w)
      ((mul_le_mul_of_nonneg_left (L.signedLetters_escape_sum_le hr hA.approximate.one_mem
        hA.approximate.inv_mem g N w hw) (by positivity)).trans_lt hsmall)
    exact ⟨x,hx,hp⟩
  refine ⟨hall,?_⟩
  rintro x ⟨w,hw,hp⟩
  obtain ⟨y,hy,hpy⟩ := hall w hw
  exact (hp.unique L hpy).symm ▸ hy
end DirectedCycles
