import DirectedCycles.HaarFiniteTrapping

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Multiplication of closure points lies in the closure of actual products. -/
theorem word_closure_mul_subset (A B : Set G) :
    closure A * closure B ⊆ closure (A*B) := by
  rintro x ⟨a,ha,b,hb,rfl⟩
  exact map_mem_closure₂' continuous_const_mul continuous_mul_const ha hb
    (fun _ hx _ hy => Set.mul_mem_mul hx hy)

/-- Finite products of closure points are limits of the corresponding
finite products of actual points. -/
theorem word_closure_power_subset (A : Set G) (n : ℕ) :
    (closure A)^n ⊆ closure (A^n) := by
  induction n with
  | zero => exact subset_closure
  | succ n ih =>
      rw [pow_succ,pow_succ]
      exact (Set.mul_subset_mul_right ih).trans (word_closure_mul_subset _ _)

/-- A finite power of a precompact set is precompact. -/
theorem compact_closure_word_power [T2Space G] {U : Set G}
    (hU : IsCompact (closure U)) (n : ℕ) : IsCompact (closure (U^n)) :=
  (compact_set_word_power hU n).closure_of_subset (Set.pow_subset_pow_left subset_closure)

/-- Closure preserves the symmetry of actual word powers. -/
theorem symmetric_closure_word_power {Q : Set G} (hQi : Q⁻¹ = Q) (n : ℕ) :
    (closure (Q^n))⁻¹ = closure (Q^n) := by
  rw [inv_closure,← inv_pow,hQi]
end DirectedCycles
