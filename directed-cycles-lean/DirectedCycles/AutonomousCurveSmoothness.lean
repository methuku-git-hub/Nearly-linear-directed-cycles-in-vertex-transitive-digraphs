import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An actual solution of a smooth autonomous differential equation is smooth.
This is regularity of an already constructed curve, with no existence axiom. -/
theorem contDiffAt_of_autonomous_derivative (f : ℝ → E) (V : E → E)
    (hV : ContDiffAt ℝ ∞ V (f 0))
    (hder : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), HasDerivAt f (V (f t)) t) :
    ContDiffAt ℝ ∞ f 0 := by
  rw [contDiffAt_infty]
  intro n
  induction n with
  | zero =>
    exact contDiffAt_zero.2 ⟨{t | HasDerivAt f (V (f t)) t},hder,
      fun t ht => ht.continuousAt.continuousWithinAt⟩
  | succ n ih =>
    apply contDiffAt_succ_iff_hasFDerivAt.2
    let f' : ℝ → ℝ →L[ℝ] E := fun t => (ContinuousLinearMap.id ℝ ℝ).smulRight (V (f t))
    refine ⟨f',⟨{t | HasDerivAt f (V (f t)) t},hder,?_⟩,?_⟩
    · intro t ht
      exact ht.hasFDerivAt
    · exact contDiffAt_const.smulRight ((hV.of_le (by simp)).comp 0 ih)
end DirectedCycles
