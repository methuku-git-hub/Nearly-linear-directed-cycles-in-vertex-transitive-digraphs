import DirectedCycles.GleasonLieAlgebra
import DirectedCycles.GleasonTrotterContinuity
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
namespace DirectedCycles
namespace GleasonLieAlgebra
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [IsTopologicalGroup G] [LocallyCompactSpace G]

instance : IsTopologicalAddGroup (GleasonLieAlgebra D) where
  continuous_add := D.continuous_trotterSum
  continuous_neg := OneParameter.continuous_scale.comp (continuous_const.prodMk continuous_id)

instance : ContinuousSMul ℝ (GleasonLieAlgebra D) := ⟨OneParameter.continuous_scale⟩

/-- Finite dimensionality follows from the proved vector-space laws,
proved continuity and proved local compactness of the actual curve space. -/
theorem finiteDimensional : FiniteDimensional ℝ (GleasonLieAlgebra D) :=
  FiniteDimensional.of_locallyCompactSpace ℝ

noncomputable instance : FiniteDimensional ℝ (GleasonLieAlgebra D) := finiteDimensional D

/-- The actual one-parameter space has a finite-dimensional Euclidean
linear homeomorphism; this does not yet assert a chart on the group. -/
theorem exists_euclidean_equiv : ∃ d : ℕ,
    Nonempty (GleasonLieAlgebra D ≃L[ℝ] EuclideanSpace ℝ (Fin d)) := by
  refine ⟨Module.finrank ℝ (GleasonLieAlgebra D),?_⟩
  apply FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
  simp
end GleasonLieAlgebra
end DirectedCycles
