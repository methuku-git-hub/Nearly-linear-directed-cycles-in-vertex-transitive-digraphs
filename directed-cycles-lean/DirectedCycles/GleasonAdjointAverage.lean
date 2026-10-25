module

public import DirectedCycles.OperatorExponentialAverage
public import DirectedCycles.GleasonHomSmoothCoordinates

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped ContDiff Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- The averaged adjoint operator constructed from the actual adjoint
representation, expressed by a convergent block exponential. -/
noncomputable def coordinateAdjointAverage (x : E) : E →L[ℝ] E :=
  operatorExponentialAverage (-(homGeneratorCLM D e (coordinateAdjointHom D e)) x)

theorem coordinateAdjointAverage_contDiff : ContDiff ℝ ∞ (coordinateAdjointAverage D e) :=
  operatorExponentialAverage_contDiff.comp (homGeneratorCLM D e (coordinateAdjointHom D e)).contDiff.neg

@[simp] theorem coordinateAdjointAverage_zero : coordinateAdjointAverage D e (0 : E) = 1 := by
  simp only [coordinateAdjointAverage,map_zero,neg_zero,operatorExponentialAverage_zero]

/-- This is the actual averaged adjoint action along the radial curve. -/
theorem coordinateAdjointAverage_eq_integral (x : E) :
    coordinateAdjointAverage D e x =
      ∫ t in (0 : ℝ)..1, coordinateAdjoint D e (coordinateExp D e ((-t) • x)) := by
  rw [coordinateAdjointAverage,operatorExponentialAverage_eq_integral]
  congr 1
  funext t
  have h := coordinateHom_eq_exp_generator D e (coordinateAdjointHom D e) ((-t) • x)
  change coordinateAdjoint D e (coordinateExp D e ((-t) • x)) =
    NormedSpace.exp ((homGeneratorCLM D e (coordinateAdjointHom D e)) ((-t) • x)) at h
  rw [h,map_smul,neg_smul,smul_neg]

/-- The averaged adjoint is invertible on a genuine neighbourhood of the
origin; invertibility is derived from its value there. -/
theorem coordinateAdjointAverage_eventually_isUnit :
    ∀ᶠ x : E in 𝓝 0, IsUnit (coordinateAdjointAverage D e x) := by
  have h := (coordinateAdjointAverage_contDiff D e).continuous.continuousAt.preimage_mem_nhds
    (Units.isOpen.mem_nhds (show IsUnit (coordinateAdjointAverage D e (0 : E)) by simp))
  exact h

/-- The inverse averaged adjoint is smooth at every point where the
actual averaged operator is invertible. -/
theorem coordinateAdjointAverage_inverse_contDiffAt (x : E)
    (hx : IsUnit (coordinateAdjointAverage D e x)) :
    ContDiffAt ℝ ∞ (fun y => Ring.inverse (coordinateAdjointAverage D e y)) x := by
  obtain ⟨u,hu⟩ := hx
  have h := contDiffAt_ringInverse ℝ (n := ∞) u
  rw [hu] at h
  exact h.comp x (coordinateAdjointAverage_contDiff D e).contDiffAt

end DirectedCycles.GleasonLieAlgebra
