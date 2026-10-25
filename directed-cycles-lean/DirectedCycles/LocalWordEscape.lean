module

public import DirectedCycles.LocalSmallWordProducts
public import DirectedCycles.LocalRestrictedCostWords

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Escape of a word uses the actual unique product if it is fully defined,
and is one otherwise, as in BGT Theorem 8.1. -/
noncomputable def wordEscape (A : Set G) (l : List G) : ℝ := by
  classical
  exact if h : ∃ x, L.Product l x then L.escapeNorm A (Classical.choose h) else 1

theorem wordEscape_of_product {A : Set G} {l : List G} {x : G} (hp : L.Product l x) :
    L.wordEscape A l = L.escapeNorm A x := by
  classical
  unfold wordEscape
  rw [dite_eq_left ⟨x,hp⟩]
  congr 1
  exact (Classical.choose_spec (show ∃ x, L.Product l x from ⟨x,hp⟩)).unique L hp

theorem wordEscape_of_undefined {A : Set G} {l : List G} (h : ¬ ∃ x, L.Product l x) :
    L.wordEscape A l = 1 := by
  classical
  exact dite_eq_right h

/-- The product inequality includes undefined words. If their total cost
were small, the all-bracketings existence theorem would define the product. -/
theorem wordEscape_le_of_restricted {A : Set G} (hA : L.one ∈ A)
    (hdom : ∀ a ∈ A, ∀ b ∈ A, L.Defined a b) {P : ℝ} (hP : 1 ≤ P)
    (hbound : ∀ g, L.escapeNorm A g ≤ P*L.restrictedProductNorm A (L.escapeNorm A) g)
    (l : List G) : L.wordEscape A l ≤ P*(l.map (L.escapeNorm A)).sum := by
  have hP0 : 0 ≤ P := by linarith
  have hw := L.escapeNorm_nonneg hA
  by_cases hdef : ∃ x, L.Product l x
  · obtain ⟨x,hx⟩ := hdef
    rw [L.wordEscape_of_product hx]
    rcases hx.restrictedCost_or_exit L hw with hc | ⟨y,r,hy,hc,hcost⟩
    · exact (hbound x).trans (mul_le_mul_of_nonneg_left (L.restrictedProductNorm_le_cost hw hc) hP0)
    · have hh := (hbound y).trans (mul_le_mul_of_nonneg_left (L.restrictedProductNorm_le_cost hw hc) hP0)
      rw [L.escapeNorm_eq_one_of_not_mem hA hy] at hh
      exact (L.escapeNorm_le_one hA x).trans (hh.trans (mul_le_mul_of_nonneg_left hcost hP0))
  · rw [L.wordEscape_of_undefined hdef]
    by_contra hn
    have hsmall : P*(l.map (L.escapeNorm A)).sum < 1 := lt_of_not_ge hn
    obtain ⟨x,_,hx,_⟩ := L.small_word_product_exists hA hdom hP hbound l hsmall
    exact hdef ⟨x,hx⟩
end LocalGroupAlgebra
end DirectedCycles
