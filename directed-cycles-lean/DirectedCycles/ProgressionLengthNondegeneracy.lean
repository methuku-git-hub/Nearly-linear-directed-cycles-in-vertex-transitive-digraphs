import DirectedCycles.ProgressionShrinkingArithmetic
import Mathlib.Order.Filter.Finite

set_option autoImplicit false
namespace DirectedCycles

/-- Appending the central scale and applying one fixed shrinking factor
preserves every coordinate's divergence along the original filter. -/
theorem central_progression_lengths_tendsto {ι : Type*} {F : Filter ι} {r : ℕ}
    (N : ι → Fin r → ℕ) (n : ι → ℕ)
    (hN : ∀ j, Filter.Tendsto (fun i => N i j) F Filter.atTop)
    (hn : Filter.Tendsto n F Filter.atTop) {T : ℕ} (hT : 0 < T) :
    ∀ j : Fin (r+1), Filter.Tendsto (fun i => (Fin.lastCases (n i) (N i) j)/T) F Filter.atTop := by
  intro j
  induction j using Fin.lastCases with
  | last =>
    simpa only [Fin.lastCases_last] using tendsto_nat_shrunk_length hn hT
  | cast j =>
    simpa only [Fin.lastCases_castSucc] using tendsto_nat_shrunk_length (hN j) hT

/-- The fixed commutator-domain threshold holds simultaneously in all
coordinates on an actual filter-large set of indices. -/
theorem central_progression_budget_eventually {ι : Type*} {F : Filter ι} {r : ℕ}
    (N : ι → Fin r → ℕ) (n : ι → ℕ)
    (hN : ∀ j, Filter.Tendsto (fun i => N i j) F Filter.atTop)
    (hn : Filter.Tendsto n F Filter.atTop) {T : ℕ} (hT : 0 < T) (c : ℕ) :
    ∀ᶠ i in F, ∀ j : Fin (r+1), 4^(c+2) ≤ (Fin.lastCases (n i) (N i) j)/T := by
  have hh := central_progression_lengths_tendsto N n hN hn hT
  exact Filter.eventually_all.2 (fun j => (hh j).eventually (Filter.eventually_ge_atTop _))
end DirectedCycles
