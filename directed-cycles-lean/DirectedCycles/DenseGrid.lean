module

public import DirectedCycles.Basic
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- A sufficiently large subset of a Cartesian grid determines every
polynomial of bounded total degree. -/
theorem dense_grid_polynomial_zero {n : ℕ} (S : Finset ℚ) (F : Finset (Fin n → ℚ))
    (hF : F ⊆ Fintype.piFinset (fun _ : Fin n => S)) (d : ℕ)
    (hlarge : (d : ℚ≥0) / S.card < (F.card : ℚ≥0) / (S.card : ℚ≥0)^n)
    (p : MvPolynomial (Fin n) ℚ) (hp : p.totalDegree ≤ d)
    (hz : ∀ x ∈ F, MvPolynomial.eval x p = 0) : p = 0 := by
  classical
  by_contra hne
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hne S
  have hsub : F ⊆ (Fintype.piFinset (fun _ : Fin n => S)).filter (fun x => MvPolynomial.eval x p = 0) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hF hx,hz x hx⟩
  have hcard := Finset.card_le_card hsub
  have hfrac : (F.card : ℚ≥0) / (S.card : ℚ≥0)^n ≤ (d : ℚ≥0)/S.card := by
    calc (F.card : ℚ≥0) / (S.card : ℚ≥0)^n ≤
        (((Fintype.piFinset (fun _ : Fin n => S)).filter (fun x => MvPolynomial.eval x p = 0)).card : ℚ≥0) /
          (S.card : ℚ≥0)^n := by gcongr
         _ ≤ (p.totalDegree : ℚ≥0)/S.card := hsz
         _ ≤ (d : ℚ≥0)/S.card := by gcongr
  exact (not_lt_of_ge hfrac) hlarge

/-- Equality of low-degree polynomials follows from agreement on such a
large subset of a grid. -/
theorem dense_grid_polynomial_ext {n : ℕ} (S : Finset ℚ) (F : Finset (Fin n → ℚ))
    (hF : F ⊆ Fintype.piFinset (fun _ : Fin n => S)) (d : ℕ)
    (hlarge : (d : ℚ≥0) / S.card < (F.card : ℚ≥0) / (S.card : ℚ≥0)^n)
    (p q : MvPolynomial (Fin n) ℚ) (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d)
    (h : ∀ x ∈ F, MvPolynomial.eval x p = MvPolynomial.eval x q) : p = q := by
  apply sub_eq_zero.mp
  apply dense_grid_polynomial_zero S F hF d hlarge
  · exact (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq)
  · intro x hx
    rw [map_sub,h x hx,sub_self]

end DirectedCycles
