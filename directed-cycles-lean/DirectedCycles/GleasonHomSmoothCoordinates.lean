module

public import DirectedCycles.GleasonHomGenerator
public import DirectedCycles.GleasonAdjointCurves

@[expose] public section

set_option autoImplicit false
open scoped ContDiff
namespace DirectedCycles.GleasonLieAlgebra
variable {G E A : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Finite dimensionality makes the constructed generator map continuous. -/
noncomputable def homGeneratorCLM (F : ContinuousMonoidHom G A) : E →L[ℝ] A :=
  { homGeneratorLinear D e F with cont := (homGeneratorLinear D e F).continuous_of_finiteDimensional }

theorem coordinateHom_eq_exp_generator (F : ContinuousMonoidHom G A) (x : E) :
    F (coordinateExp D e x) = NormedSpace.exp (homGeneratorCLM D e F x) := by
  change F (coordinateExp D e x) = NormedSpace.exp (homGenerator D e F x)
  simpa only [one_smul] using homGenerator_exp D e F x 1

/-- Every continuous normed-algebra-valued representation is smooth in
the constructed exponential coordinates, before smoothness of the group
operations themselves has been established. -/
theorem coordinateHom_contDiff (F : ContinuousMonoidHom G A) :
    ContDiff ℝ ∞ (fun x : E => F (coordinateExp D e x)) := by
  have he : ContDiff ℝ ∞ (NormedSpace.exp : A → A) :=
    (show AnalyticOnNhd ℝ (NormedSpace.exp : A → A) Set.univ from fun x _ => NormedSpace.exp_analytic x).contDiff
  have h := he.comp (homGeneratorCLM D e F).contDiff
  have heq : (fun x : E => F (coordinateExp D e x)) =
      (fun x : E => NormedSpace.exp (homGeneratorCLM D e F x)) := funext (coordinateHom_eq_exp_generator D e F)
  rw [heq]
  exact h

/-- The actual finite-dimensional adjoint representation as a continuous
homomorphism into the full operator algebra. -/
noncomputable def coordinateAdjointHom : ContinuousMonoidHom G (E →L[ℝ] E) where
  toFun := coordinateAdjoint D e
  map_one' := coordinateAdjoint_one D e
  map_mul' := coordinateAdjoint_mul D e
  continuous_toFun := continuous_coordinateAdjoint D e

/-- The adjoint action is jointly smooth in the vector coordinates. -/
theorem coordinateAdjoint_contDiff :
    ContDiff ℝ ∞ (fun x : E => coordinateAdjoint D e (coordinateExp D e x)) :=
  coordinateHom_contDiff D e (coordinateAdjointHom D e)

end DirectedCycles.GleasonLieAlgebra
