module

public import DirectedCycles.LocalEscapeNorm

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A strict escape cutoff supplies every required finite power, including
its all-bracketings multiplication domain. -/
theorem powerIn_of_escapeNorm_lt {A : Set G} (hA : L.one ∈ A) {x : G} {C : ℕ}
    (hx : L.escapeNorm A x < 1/((C : ℝ)+1)) : ∀ j ≤ C, L.PowerIn A x j := by
  intro j hj
  by_cases hj0 : j = 0
  · subst j; exact (L.powerIn_zero A x).2 hA
  by_contra hbad
  have hlow := L.inv_le_escapeNorm_of_not_powerIn hA hbad
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hupper : (j : ℝ) ≤ (C : ℝ)+1 := by exact_mod_cast (by omega : j ≤ C+1)
  have hcompare := one_div_le_one_div_of_le hjpos hupper
  linarith
end LocalGroupAlgebra
end DirectedCycles
