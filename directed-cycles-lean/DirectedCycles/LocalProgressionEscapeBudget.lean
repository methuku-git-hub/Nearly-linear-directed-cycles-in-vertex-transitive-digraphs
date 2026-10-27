module

public import DirectedCycles.LocalSignedWords

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- One integer shrinking factor controls every coordinate length. It does
not depend on the lengths, and allows repeated letters of either sign. -/
theorem progression_escape_budget {r : ℕ} (N : Fin r → ℕ) (e : Fin r → ℝ)
    {C P : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) {T : ℕ} (hT : 0 < T)
    (hlarge : P*C*(r : ℝ) < T)
    (he : ∀ i, e i ≤ C/((N i : ℝ)+1)) :
    P * (∑ i : Fin r, ((N i/T : ℕ) : ℝ)*e i) < 1 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hb : ∀ i, ((N i/T : ℕ) : ℝ)*e i ≤ C/(T : ℝ) := by
    intro i
    have hdiv : ((N i/T : ℕ) : ℝ)*(T : ℝ) ≤ (N i : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self (N i) T
    have hratio : ((N i/T : ℕ) : ℝ)/((N i : ℝ)+1) ≤ 1/(T : ℝ) :=
      (div_le_div_iff₀ (by positivity) hTr).2 (by nlinarith)
    calc
      ((N i/T : ℕ) : ℝ)*e i ≤ ((N i/T : ℕ) : ℝ)*(C/((N i : ℝ)+1)) :=
        mul_le_mul_of_nonneg_left (he i) (by positivity)
      _ = C*(((N i/T : ℕ) : ℝ)/((N i : ℝ)+1)) := by ring
      _ ≤ C*(1/(T : ℝ)) := mul_le_mul_of_nonneg_left hratio hC
      _ = C/(T : ℝ) := by ring
  have hs : (∑ i : Fin r, ((N i/T : ℕ) : ℝ)*e i) ≤ (r : ℝ)*(C/(T : ℝ)) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  apply (mul_le_mul_of_nonneg_left hs hP).trans_lt
  rw [show P*((r : ℝ)*(C/(T : ℝ))) = P*C*(r : ℝ)/(T : ℝ) by ring]
  exact (div_lt_one hTr).2 hlarge

/-- A fixed shrinking factor constructs all words in a strong approximate
group from coordinate-wise reciprocal-length escape bounds. -/
theorem strong_local_shrunk_progression {G : Type*} [Fintype G]
    (L : LocalGroupAlgebra G) (hd : L.DivisionClosed) (hr : L.Reversible)
    {K : ℕ} {A : Finset G} (hA : IsStrongLocalFiniteApproximateGroup L K A)
    {r : ℕ} {C : ℝ} (hC : 0 ≤ C) :
    ∃ T : ℕ, 0 < T ∧ ∀ (g : Fin r → G) (N : Fin r → ℕ),
      (∀ i, L.escapeNorm A (g i) ≤ C/((N i : ℝ)+1)) →
      (∀ w : List (Fin r × Bool), (∀ i, w.countP (fun a => a.1 = i) ≤ N i/T) →
        ∃ x ∈ A, L.Product (L.signedLetters g w) x) ∧
      L.wordProgression g (fun i => N i/T) ⊆ A := by
  let P : ℝ := 8*1000*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  obtain ⟨T,hT⟩ := exists_nat_gt (max 0 (P*C*(r : ℝ)))
  have hT0 : 0 < T := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hT)
  refine ⟨T,hT0,?_⟩
  intro g N he
  exact strong_local_wordProgression_defined L hd hr hA g (fun i => N i/T)
    (progression_escape_budget N (fun i => L.escapeNorm A (g i)) hC hP hT0
      (lt_of_le_of_lt (le_max_right _ _) hT) he)
end DirectedCycles
