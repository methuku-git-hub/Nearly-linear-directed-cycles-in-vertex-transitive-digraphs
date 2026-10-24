import DirectedCycles.LocalProgressionEscapeBudget
import DirectedCycles.LocalControlledGeneratorLifts
import DirectedCycles.LocalWordProgressionMaps

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem wordProgression_mono {r : ℕ} (g : Fin r → G) {M N : Fin r → ℕ}
    (hMN : ∀ i, M i ≤ N i) : L.wordProgression g M ⊆ L.wordProgression g N := by
  rintro x ⟨w,hw,hp⟩
  exact ⟨w,fun i => (hw i).trans (hMN i),hp⟩

namespace CentralQuotientData
variable {L} {P : Set G} (D : L.CentralQuotientData P) [Fintype G]

/-- A uniform lift bound gives a single shrinking factor for every tuple
and every length choice. Every lifted signed word is an actual product in
the source, and its actual quotient image lies in the original progression. -/
theorem controlled_progression_words (hd : L.DivisionClosed) (hr : L.Reversible)
    (B : Finset G) {K : ℕ} (hB : IsStrongLocalFiniteApproximateGroup L K B)
    (hBD : (B : Set G) ⊆ D.small) {C : ℝ} (hC : 0 ≤ C)
    (hcontrol : ∀ y ∈ D.finiteImage B, ∃ x : D.small, x.val ∈ B ∧ D.project x = y ∧
      L.escapeNorm B x.val ≤ C*D.algebra.escapeNorm (D.finiteImage B) y)
    (r : ℕ) :
    ∃ T : ℕ, 0 < T ∧ ∀ (g : Fin r → D.Carrier) (N : Fin r → ℕ),
      (∀ i, g i ∈ D.finiteImage B) →
      (∀ i, ∀ n ≤ N i, D.algebra.PowerIn (D.finiteImage B) (g i) n) →
      ∃ u : Fin r → D.small,
        (∀ i, (u i).val ∈ B ∧ D.project (u i) = g i ∧ L.escapeNorm B (u i).val ≤ C/((N i : ℝ)+1)) ∧
        (∀ w : List (Fin r × Bool), (∀ i, w.countP (fun a => a.1 = i) ≤ N i/T) →
          ∃ x ∈ B, L.Product (L.signedLetters (fun i => (u i).val) w) x) ∧
        L.wordProgression (fun i => (u i).val) (fun i => N i/T) ⊆ B ∧
        D.project '' {x : D.small | x.val ∈ L.wordProgression (fun i => (u i).val) (fun i => N i/T)} ⊆
          D.algebra.wordProgression g N := by
  obtain ⟨T,hT,hwords⟩ := strong_local_shrunk_progression L hd hr hB (r := r) hC
  refine ⟨T,hT,?_⟩
  intro g N hg hpowers
  obtain ⟨u,hu⟩ := D.controlled_generator_lifts B hC hcontrol g N hg hpowers
  obtain ⟨hdefined,hsub⟩ := hwords (fun i => (u i).val) N (fun i => (hu i).2.2)
  have hall : ∀ w : List (Fin r × Bool), (∀ i, w.countP (fun a => a.1 = i) ≤ N i/T) →
      ∃ x ∈ D.small, L.Product (L.signedLetters (fun i => (u i).val) w) x := by
    intro w hw
    obtain ⟨x,hx,hp⟩ := hdefined w hw
    exact ⟨x,hBD hx,hp⟩
  refine ⟨u,hu,hdefined,hsub,?_⟩
  rintro _ ⟨x,⟨w,hw,hp⟩,rfl⟩
  have hpr := D.project_signedWord u (fun i => N i/T) hall w hw x hp
  have hgen : (fun i => D.project (u i)) = g := funext fun i => (hu i).2.1
  rw [hgen] at hpr
  exact ⟨w,fun i => (hw i).trans (Nat.div_le_self _ _),hpr⟩
end CentralQuotientData
end LocalGroupAlgebra
end DirectedCycles
