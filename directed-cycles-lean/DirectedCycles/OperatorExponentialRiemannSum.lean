import DirectedCycles.OperatorExponentialAverage
import DirectedCycles.LipschitzRiemannSum
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
namespace DirectedCycles

/-- An exponential curve is Lipschitz on the compact unit interval. -/
theorem normedAlgebra_exp_lipschitz_unitInterval {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (T : A) :
    ∃ L : NNReal, LipschitzOnWith L (fun t : ℝ => NormedSpace.exp (t • T)) (Set.Icc 0 1) := by
  have hc : Continuous (fun t : ℝ => NormedSpace.exp (t • T)) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_exp_smul_const T t).continuousAt)
  have hd : Continuous (fun t : ℝ => NormedSpace.exp (t • T)*T) := hc.mul continuous_const
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hd.continuousOn
  refine ⟨⟨max M 0,le_max_right _ _⟩,?_⟩
  apply (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_exp_smul_const T t).hasDerivWithinAt)
  intro t ht
  change ‖NormedSpace.exp (t • T)*T‖ ≤ max M 0
  exact (hM t ht).trans (le_max_left _ _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The discrete exponential averages converge to the smooth block formula. -/
theorem operatorExponentialAverage_riemann_tendsto (T : E →L[ℝ] E) :
    Tendsto (fun n : ℕ => (1/(n : ℝ)) •
      (∑ k ∈ Finset.range n, NormedSpace.exp (((k : ℝ)/n) • T))) atTop
      (𝓝 (operatorExponentialAverage T)) := by
  obtain ⟨L,hL⟩ := normedAlgebra_exp_lipschitz_unitInterval T
  rw [operatorExponentialAverage_eq_integral]
  exact lipschitz_riemann_sum_tendsto hL

end DirectedCycles
