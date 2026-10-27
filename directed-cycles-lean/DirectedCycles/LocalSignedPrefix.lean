module

public import DirectedCycles.LocalSignedWords
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Reindex a signed word into the first coordinates of the extended tuple. -/
def signedWordPrefix {r : ℕ} (w : List (Fin r × Bool)) : List (Fin (r+1) × Bool) :=
  w.map (fun a => (a.1.castSucc,a.2))

theorem signedWordPrefix_count_castSucc {r : ℕ} (w : List (Fin r × Bool)) (i : Fin r) :
    (signedWordPrefix w).countP (fun a => a.1 = i.castSucc) = w.countP (fun a => a.1 = i) := by
  simp [signedWordPrefix,List.countP_map,Function.comp_def]

theorem signedWordPrefix_count_last {r : ℕ} (w : List (Fin r × Bool)) :
    (signedWordPrefix w).countP (fun a => a.1 = Fin.last r) = 0 := by
  simp [signedWordPrefix,List.countP_map,Function.comp_def]

namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem signedLetters_prefix {r : ℕ} (g : Fin (r+1) → G) (w : List (Fin r × Bool)) :
    L.signedLetters g (signedWordPrefix w) = L.signedLetters (fun i => g i.castSucc) w := by
  simp only [signedLetters,signedWordPrefix,List.map_map]
  rfl

theorem signedWords_prefix_defined {r : ℕ} (g : Fin (r+1) → G) (N : Fin (r+1) → ℕ) (S : Set G)
    (hall : ∀ w : List (Fin (r+1) × Bool), (∀ i, w.countP (fun a => a.1 = i) ≤ N i) →
      ∃ x ∈ S, L.Product (L.signedLetters g w) x) :
    ∀ w : List (Fin r × Bool), (∀ i, w.countP (fun a => a.1 = i) ≤ N i.castSucc) →
      ∃ x ∈ S, L.Product (L.signedLetters (fun i => g i.castSucc) w) x := by
  intro w hw
  have hh := hall (signedWordPrefix w) (fun i => by
    induction i using Fin.lastCases with
    | last => rw [signedWordPrefix_count_last]; exact Nat.zero_le _
    | cast i => rw [signedWordPrefix_count_castSucc]; exact hw i)
  simpa only [L.signedLetters_prefix] using hh
end LocalGroupAlgebra
end DirectedCycles
