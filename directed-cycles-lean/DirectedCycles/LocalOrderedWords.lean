import DirectedCycles.LocalSignedWords
import DirectedCycles.LocalSignedPowers
import DirectedCycles.LocalProductInversion
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

set_option autoImplicit false
namespace DirectedCycles

/-- The specified coordinate order is encoded by an actual signed word. -/
def orderedSignedWord {r : ℕ} (k : Fin r → ℤ) : List (Fin r × Bool) :=
  (List.ofFn (fun i => List.replicate (k i).natAbs (i,decide (0 ≤ k i)))).flatten

theorem orderedSignedWord_count {r : ℕ} (k : Fin r → ℤ) (i : Fin r) :
    (orderedSignedWord k).countP (fun a => a.1 = i) = (k i).natAbs := by
  simp only [orderedSignedWord,List.countP_flatten,List.map_ofFn,Function.comp_apply,List.sum_ofFn,List.countP_replicate]
  simp

namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

def orderedLetters {r : ℕ} (g : Fin r → G) (k : Fin r → ℤ) : List G :=
  L.signedLetters g (orderedSignedWord k)

theorem orderedLetters_eq {r : ℕ} (g : Fin r → G) (k : Fin r → ℤ) :
    L.orderedLetters g k =
      (List.ofFn (fun i => List.replicate (k i).natAbs (if 0 ≤ k i then g i else L.inv (g i)))).flatten := by
  simp only [orderedLetters,signedLetters,orderedSignedWord,List.map_flatten,List.map_ofFn]
  congr 2
  funext i
  simp

theorem orderedLetters_succ {r : ℕ} (g : Fin (r+1) → G) (k : Fin (r+1) → ℤ) :
    L.orderedLetters g k = L.orderedLetters (fun i => g i.castSucc) (fun i => k i.castSucc) ++
      List.replicate (k (Fin.last r)).natAbs (if 0 ≤ k (Fin.last r) then g (Fin.last r) else L.inv (g (Fin.last r))) := by
  rw [L.orderedLetters_eq,List.ofFn_succ_last,List.flatten_append]
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil,L.orderedLetters_eq]

theorem orderedLetters_zero {r : ℕ} (g : Fin r → G) : L.orderedLetters g (fun _ => 0) = [] := by
  simp [L.orderedLetters_eq]

/-- Ordered coordinates inherit the actual domain from the signed-word
progression, with precisely the given coordinate-length bounds. -/
theorem orderedLetters_product_of_words {r : ℕ} (g : Fin r → G) (N : Fin r → ℕ) (S : Set G)
    (hwords : ∀ w : List (Fin r × Bool), (∀ i, w.countP (fun a => a.1 = i) ≤ N i) →
      ∃ x ∈ S, L.Product (L.signedLetters g w) x)
    (k : Fin r → ℤ) (hk : ∀ i, (k i).natAbs ≤ N i) :
    ∃ x ∈ S, L.Product (L.orderedLetters g k) x :=
  hwords (orderedSignedWord k) (fun i => by rw [orderedSignedWord_count]; exact hk i)

/-- Each ordered signed block has the corresponding actual segment value. -/
theorem PowerSegment.signed_block_product {u : G} {N : ℕ} (p : L.PowerSegment u N)
    (hr : L.Reversible) (k : ℤ) (hk : k.natAbs ≤ N) :
    L.Product (List.replicate k.natAbs (if 0 ≤ k then u else L.inv u)) (p.signedPower k) := by
  rcases Int.eq_nat_or_neg k with ⟨n,rfl | rfl⟩
  · simpa only [Int.natAbs_natCast,Int.natCast_nonneg,ite_eq_left,p.signedPower_nat] using p.product n hk
  · by_cases hn : n = 0
    · subst n
      simpa only [Nat.cast_zero,neg_zero,Int.natAbs_zero,List.replicate_zero,p.signedPower_zero] using Product.nil (L := L)
    · have hnegative : ¬ (0 : ℤ) ≤ -(n : ℤ) := by omega
      have hh := (p.product n (by simpa only [Int.natAbs_neg,Int.natAbs_natCast] using hk)).reverse_inv L hr
      simpa only [Int.natAbs_neg,Int.natAbs_natCast,ite_eq_right hnegative,p.signedPower_neg_nat,
        List.reverse_replicate,List.map_replicate] using hh
end LocalGroupAlgebra
end DirectedCycles
