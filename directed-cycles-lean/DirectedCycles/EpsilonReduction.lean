module

public import DirectedCycles.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- It is enough to prove the exact asymptotic target for errors below one. -/
theorem main_of_small_errors
    (h : ∀ eps : ℝ, 0 < eps → eps < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ X : Digraph (Fin n), Loopless X → Connected X → VertexTransitive X →
        ∃ C : Cycle X, (n : ℝ)^(1-eps) ≤ C.length) : MainTheorem := by
  intro eps heps
  let eta := min eps (1/2)
  have heta : 0 < eta := lt_min heps (by norm_num)
  have heta1 : eta < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨N,hN⟩ := h eta heta heta1
  refine ⟨max N 1,?_⟩
  intro n hn X hloop hconn htrans
  obtain ⟨C,hC⟩ := hN n ((le_max_left N 1).trans hn) X hloop hconn htrans
  refine ⟨C,?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right N 1).trans hn
  exact (Real.rpow_le_rpow_of_exponent_le hn1 (by have := min_le_left eps (1/2); dsimp only [eta]; linarith)).trans hC

end DirectedCycles
