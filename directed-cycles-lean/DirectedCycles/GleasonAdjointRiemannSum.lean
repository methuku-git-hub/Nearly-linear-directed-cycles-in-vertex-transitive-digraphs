import DirectedCycles.GleasonAdjointAverage
import DirectedCycles.OperatorExponentialRiemannSum

set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

theorem coordinateAdjoint_negative_radial_exp (x : E) (t : ℝ) :
    coordinateAdjoint D e (coordinateExp D e ((-t) • x)) =
      NormedSpace.exp (t • (-(homGeneratorCLM D e (coordinateAdjointHom D e)) x)) := by
  have h := coordinateHom_eq_exp_generator D e (coordinateAdjointHom D e) ((-t) • x)
  change coordinateAdjoint D e (coordinateExp D e ((-t) • x)) =
    NormedSpace.exp ((homGeneratorCLM D e (coordinateAdjointHom D e)) ((-t) • x)) at h
  rw [h,map_smul,neg_smul,smul_neg]

/-- The finite adjoint averages converge as operators to the actual
smooth averaged adjoint. -/
theorem coordinateAdjointAverage_riemann_tendsto (x : E) :
    Tendsto (fun n : ℕ => (1/(n : ℝ)) • (∑ k ∈ Finset.range n,
      coordinateAdjoint D e (coordinateExp D e ((-((k : ℝ)/n)) • x)))) atTop
      (𝓝 (coordinateAdjointAverage D e x)) := by
  simp only [coordinateAdjoint_negative_radial_exp,coordinateAdjointAverage]
  exact operatorExponentialAverage_riemann_tendsto _

/-- The vector-valued finite sums used in the conjugate-product
calculation converge to the averaged adjoint applied to the vector. -/
theorem coordinateAdjointAverage_riemann_apply_tendsto (x z : E) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (1/(n : ℝ)) •
      (coordinateAdjoint D e (coordinateExp D e ((-((k : ℝ)/n)) • x)) z)) atTop
      (𝓝 (coordinateAdjointAverage D e x z)) := by
  have h := ((ContinuousLinearMap.apply ℝ E z).continuous.tendsto _).comp
    (coordinateAdjointAverage_riemann_tendsto D e x)
  simpa only [Function.comp_def,ContinuousLinearMap.apply_apply,smul_apply,
    sum_apply,Finset.smul_sum] using h

end DirectedCycles.GleasonLieAlgebra
