module

public import DirectedCycles.LocalOrderedWords
public import DirectedCycles.SignedCoordinateBox
public import DirectedCycles.LocalWordProgressionMaps

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- All signed words in the given coordinate budget have actual products
in the stated window, including every contiguous bracketing. -/
def SignedWordsIn {r : ℕ} (g : Fin r → G) (N : Fin r → ℕ) (S : Set G) : Prop :=
  ∀ w : List (Fin r × Bool), (∀ i, w.countP (fun a => a.1 = i) ≤ N i) →
    ∃ x ∈ S, L.Product (L.signedLetters g w) x

/-- Choose the unique actual product for each ordered coordinate vector. -/
noncomputable def orderedGrid {r : ℕ} {g : Fin r → G} {N : Fin r → ℕ} {S : Set G}
    (h : L.SignedWordsIn g N S) (k : SignedCoordinates N) : S :=
  ⟨Classical.choose (L.orderedLetters_product_of_words g N S h (fun i => (k i).val) k.bound),
    (Classical.choose_spec (L.orderedLetters_product_of_words g N S h (fun i => (k i).val) k.bound)).1⟩

theorem orderedGrid_product {r : ℕ} {g : Fin r → G} {N : Fin r → ℕ} {S : Set G}
    (h : L.SignedWordsIn g N S) (k : SignedCoordinates N) :
    L.Product (L.orderedLetters g (fun i => (k i).val)) (L.orderedGrid h k).val :=
  (Classical.choose_spec (L.orderedLetters_product_of_words g N S h (fun i => (k i).val) k.bound)).2

theorem orderedGrid_mem_progression {r : ℕ} {g : Fin r → G} {N : Fin r → ℕ} {S : Set G}
    (h : L.SignedWordsIn g N S) (k : SignedCoordinates N) :
    (L.orderedGrid h k).val ∈ L.wordProgression g N :=
  ⟨orderedSignedWord (fun i => (k i).val),fun i => by rw [orderedSignedWord_count]; exact k.bound i,
    L.orderedGrid_product h k⟩

/-- Proper ordered coordinates give the full box cardinality in the source. -/
theorem orderedGrid_card_le {r : ℕ} {g : Fin r → G} {N : Fin r → ℕ} {S : Finset G}
    (h : L.SignedWordsIn g N S) (hinj : Function.Injective (L.orderedGrid h)) :
    (∏ i, (2*N i+1)) ≤ S.card := by
  have hh := Fintype.card_le_of_injective (L.orderedGrid h) hinj
  change Fintype.card (SignedCoordinates N) ≤ Fintype.card ↥S at hh
  simpa only [signedCoordinates_card,Fintype.card_coe] using hh

namespace CentralQuotientData
variable {L} {P : Set G} (D : L.CentralQuotientData P)

/-- The constructed ordered grid maps to exactly the same quotient words. -/
theorem project_orderedGrid {r : ℕ} (g : Fin r → D.small) (N : Fin r → ℕ)
    (h : L.SignedWordsIn (fun i => (g i).val) N D.small)
    (hq : D.algebra.SignedWordsIn (fun i => D.project (g i)) N Set.univ)
    (k : SignedCoordinates N) :
    D.project (L.orderedGrid h k) = (D.algebra.orderedGrid hq k).val := by
  have hp := D.project_signedWord g N h (orderedSignedWord (fun i => (k i).val))
    (fun i => by rw [orderedSignedWord_count]; exact k.bound i) (L.orderedGrid h k) (L.orderedGrid_product h k)
  exact hp.unique D.algebra (D.algebra.orderedGrid_product hq k)

/-- Properness of the actual quotient grid distinguishes source prefix coordinates. -/
theorem projected_orderedGrid_injective {r : ℕ} (g : Fin r → D.small) (N : Fin r → ℕ)
    (h : L.SignedWordsIn (fun i => (g i).val) N D.small)
    (hq : D.algebra.SignedWordsIn (fun i => D.project (g i)) N Set.univ)
    (hinj : Function.Injective (D.algebra.orderedGrid hq)) :
    Function.Injective (fun k => D.project (L.orderedGrid h k)) := by
  intro k l he
  apply hinj
  apply Subtype.ext
  rw [← D.project_orderedGrid g N h hq k,← D.project_orderedGrid g N h hq l]
  exact he
end CentralQuotientData
end LocalGroupAlgebra
end DirectedCycles
