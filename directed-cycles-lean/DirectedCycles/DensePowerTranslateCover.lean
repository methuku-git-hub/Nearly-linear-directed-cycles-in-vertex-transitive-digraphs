module

public import Mathlib.Combinatorics.Additive.RuzsaCovering
public import DirectedCycles.FiniteAlmostPeriods

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace FiniteAlmostPeriods
variable {G : Type*} [Group G] [DecidableEq G]

/-- Uniform finite covers of every fixed power by a dense short difference
set. Representatives are themselves in that power. -/
theorem dense_power_translate_cover (A R : Finset G) (K d : ℝ) (p : ℕ)
    (hA : IsApproximateSubgroup K (A : Set G)) (hd : 0 < d)
    (hR : R ⊆ A^16) (hcard : d*A.card ≤ R.card) (hi : R⁻¹ = R) :
    ∃ F : Finset G, F ⊆ A^p ∧ F.card ≤ ⌈K^(p+15)/d⌉₊ ∧
      A^p ⊆ F*R^2 := by
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hA.one_le
  have hAcard : (0 : ℝ) < A.card := by exact_mod_cast (show A.Nonempty from ⟨1,hA.one_mem⟩).card_pos
  have hRnon : R.Nonempty := Finset.card_pos.mp (by
    have hh := (mul_pos hd hAcard).trans_le hcard
    exact_mod_cast hh)
  have hprod : ((A^p*R).card : ℝ) ≤ (K^(p+15)/d)*R.card := by
    have hsub : A^p*R ⊆ A^(p+16) := by
      calc A^p*R ⊆ A^p*A^16 := Finset.mul_subset_mul (Finset.Subset.refl _) hR
           _ = A^(p+16) := by rw [← pow_add]
    have hc : ((A^p*R).card : ℝ) ≤ (A^(p+16)).card := by exact_mod_cast Finset.card_le_card hsub
    have hp : ((A^(p+16)).card : ℝ) ≤ K^(p+15)*A.card := by
      simpa only [show p+16-1=p+15 by omega] using hA.card_pow_le (n := p+16)
    have hdiv : (A.card : ℝ) ≤ R.card/d := (le_div_iff₀ hd).mpr (by nlinarith [hcard])
    calc
      ((A^p*R).card : ℝ) ≤ K^(p+15)*A.card := hc.trans hp
      _ ≤ K^(p+15)*(R.card/d) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = (K^(p+15)/d)*R.card := by ring
  obtain ⟨F,hFA,hFc,hcov⟩ := Finset.ruzsa_covering_mul hRnon hprod
  refine ⟨F,hFA,?_,?_⟩
  · exact_mod_cast hFc.trans (Nat.le_ceil _)
  · simpa only [div_eq_mul_inv,hi,pow_two] using hcov

omit [DecidableEq G] in
/-- Enumerating a bounded finite cover with identity padding makes the
number of representatives independent of the ambient finite group. -/
theorem bounded_cover_tuple (F : Finset G) (N : ℕ) (hF : F.card ≤ N)
    (A : Set G) (hFA : (F : Set G) ⊆ A) (hA1 : 1 ∈ A) :
    ∃ a : Fin N → G, (F : Set G) ⊆ Set.range a ∧ ∀ j, a j ∈ A := by
  classical
  let e := Fintype.equivFin F
  let a : Fin N → G := fun j => if h : j.val < Fintype.card F then (e.symm ⟨j.val,h⟩).val else 1
  refine ⟨a,?_,?_⟩
  · intro x hx
    let i := e ⟨x,hx⟩
    have hi : i.val < N := i.isLt.trans_le (by simpa using hF)
    refine ⟨⟨i.val,hi⟩,?_⟩
    dsimp only [a]
    rw [dite_eq_left i.isLt]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x,hx⟩)
  · intro j
    dsimp only [a]
    split
    · exact hFA (e.symm _).property
    · exact hA1

end FiniteAlmostPeriods
end DirectedCycles
