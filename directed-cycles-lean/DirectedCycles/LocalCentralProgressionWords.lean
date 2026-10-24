import DirectedCycles.LocalOrderedGrid
import DirectedCycles.LocalControlledGeneratorLifts
import DirectedCycles.LocalProgressionEscapeBudget

set_option autoImplicit false
namespace DirectedCycles
/-- A numerical scale, shared by every finite component with these parameters. -/
theorem central_progression_scale_exists (K r : ℕ) (C C₀ : ℝ) :
    ∃ T : ℕ, 3 ≤ T ∧ (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)) * (max C C₀) * ((r+1 : ℕ) : ℝ) < T := by
  obtain ⟨T,hT⟩ := exists_nat_gt (max 3
    ((8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)) * (max C C₀) * ((r+1 : ℕ) : ℝ)))
  refine ⟨T,?_,(le_max_right _ _).trans_lt hT⟩
  have hh : (3 : ℝ) < T := (le_max_left _ _).trans_lt hT
  exact_mod_cast (le_of_lt hh)

namespace LocalGroupAlgebra.CentralQuotientData
variable {G : Type*} [Fintype G] {L : LocalGroupAlgebra G} {P : Set G} (D : L.CentralQuotientData P)

/-- The quotient generators and the central generator share one fixed
shrinking factor. It is independent of every coordinate length. -/
theorem controlled_central_progression_words_of_budget (hd : L.DivisionClosed) (hr : L.Reversible)
    (B : Finset G) {K : ℕ} (hB : IsStrongLocalFiniteApproximateGroup L K B)
    {C C₀ : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hcontrol : ∀ y ∈ D.finiteImage B, ∃ x : D.small, x.val ∈ B ∧ D.project x = y ∧
      L.escapeNorm B x.val ≤ C*D.algebra.escapeNorm (D.finiteImage B) y)
    (r T : ℕ) (hT : 3 ≤ T)
    (hlarge : (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)) * (max C C₀) * ((r+1 : ℕ) : ℝ) < T) : ∀ (g : Fin r → D.Carrier) (N : Fin r → ℕ),
      (∀ i, g i ∈ D.finiteImage B) →
      (∀ i, ∀ m ≤ N i, D.algebra.PowerIn (D.finiteImage B) (g i) m) →
      ∀ (u : D.small) (n : ℕ), L.escapeNorm B u.val ≤ C₀/((n : ℝ)+1) →
      ∃ v : Fin (r+1) → D.small,
        v (Fin.last r) = u ∧ (∀ i, D.project (v i.castSucc) = g i) ∧
        L.SignedWordsIn (fun i => (v i).val) (fun i => (Fin.lastCases n N i)/T) B ∧
        L.wordProgression (fun i => (v i).val) (fun i => (Fin.lastCases n N i)/T) ⊆ B := by
  let Q : ℝ := 8*1000*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hTpos : 0 < T := by omega
  intro g N hg hpowers u n hu
  obtain ⟨v,hv⟩ := D.controlled_generator_lifts B hC hcontrol g N hg hpowers
  let a : Fin (r+1) → D.small := Fin.lastCases u v
  let F : Fin (r+1) → ℕ := Fin.lastCases n N
  have he : ∀ i, L.escapeNorm B (a i).val ≤ max C C₀ / ((F i : ℝ)+1) := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      simp only [a,F,Fin.lastCases_last]
      exact hu.trans (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))
    | cast i =>
      simp only [a,F,Fin.lastCases_castSucc]
      exact (hv i).2.2.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  have hsmall := progression_escape_budget F (fun i => L.escapeNorm B (a i).val)
    (hC₀.trans (le_max_right _ _)) hQ hTpos hlarge he
  obtain ⟨hwords,hsub⟩ := strong_local_wordProgression_defined L hd hr hB
    (fun i => (a i).val) (fun i => F i/T) hsmall
  refine ⟨a,by simp only [a,Fin.lastCases_last],?_,hwords,hsub⟩
  intro i
  simpa only [a,Fin.lastCases_castSucc] using (hv i).2.1

/-- The shrinking factor depends only on K, the rank and the two lift bounds. -/
theorem controlled_central_progression_words (hd : L.DivisionClosed) (hr : L.Reversible)
    (B : Finset G) {K : ℕ} (hB : IsStrongLocalFiniteApproximateGroup L K B)
    {C C₀ : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hcontrol : ∀ y ∈ D.finiteImage B, ∃ x : D.small, x.val ∈ B ∧ D.project x = y ∧
      L.escapeNorm B x.val ≤ C*D.algebra.escapeNorm (D.finiteImage B) y)
    (r : ℕ) :
    ∃ T : ℕ, 3 ≤ T ∧ ∀ (g : Fin r → D.Carrier) (N : Fin r → ℕ),
      (∀ i, g i ∈ D.finiteImage B) →
      (∀ i, ∀ m ≤ N i, D.algebra.PowerIn (D.finiteImage B) (g i) m) →
      ∀ (u : D.small) (n : ℕ), L.escapeNorm B u.val ≤ C₀/((n : ℝ)+1) →
      ∃ v : Fin (r+1) → D.small,
        v (Fin.last r) = u ∧ (∀ i, D.project (v i.castSucc) = g i) ∧
        L.SignedWordsIn (fun i => (v i).val) (fun i => (Fin.lastCases n N i)/T) B ∧
        L.wordProgression (fun i => (v i).val) (fun i => (Fin.lastCases n N i)/T) ⊆ B := by
  obtain ⟨T,hT,hlarge⟩ := central_progression_scale_exists K r C C₀
  exact ⟨T,hT,D.controlled_central_progression_words_of_budget hd hr B hB hC hC₀ hcontrol r T hT hlarge⟩

end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
