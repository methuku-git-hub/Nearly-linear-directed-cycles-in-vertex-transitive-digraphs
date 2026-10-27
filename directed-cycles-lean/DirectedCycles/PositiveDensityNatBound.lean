module

public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A fixed positive real density gives one natural cardinal multiplier. -/
theorem positive_density_nat_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ a b : ℕ, δ*(a : ℝ) ≤ b → a ≤ J*b := by
  let J := ⌈1/δ⌉₊+1
  have hJ : 1/δ ≤ (J : ℝ) := (Nat.le_ceil (1/δ)).trans (by
    dsimp only [J]
    exact_mod_cast Nat.le_succ ⌈1/δ⌉₊)
  refine ⟨J,by dsimp only [J]; omega,?_⟩
  intro a b hab
  have ha : (a : ℝ) ≤ (b : ℝ)/δ := (le_div_iff₀ hδ).2 (by nlinarith)
  have hb := mul_le_mul_of_nonneg_right hJ (Nat.cast_nonneg b)
  have hc : (a : ℝ) ≤ (J : ℝ)*b := ha.trans (by
    calc
      (b : ℝ)/δ = (1/δ)*b := by ring
      _ ≤ (J : ℝ)*b := hb)
  exact_mod_cast hc
end DirectedCycles
