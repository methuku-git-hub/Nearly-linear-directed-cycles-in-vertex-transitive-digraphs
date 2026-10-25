module

public import DirectedCycles.GleasonExponentialChart
public import DirectedCycles.GleasonAdjoint
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Manifold.ChartedSpace

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- The constructed exponential map in any compatible linear coordinates. -/
noncomputable def coordinateExp (x : E) : G := exp D (e.symm x)

@[simp] theorem coordinateExp_zero : coordinateExp D e 0 = 1 := by simp [coordinateExp,exp_zero]

theorem coordinateExp_smul (t : ℝ) (x : E) :
    coordinateExp D e (t • x) = (toOneParameter D (e.symm x)).eval t := by
  simp only [coordinateExp,map_smul,exp_smul]

theorem continuous_coordinateExp : Continuous (coordinateExp D e) :=
  (continuous_exp D).comp e.symm.continuous

noncomputable def coordinateChart : OpenPartialHomeomorph E G :=
  e.symm.toHomeomorph.transOpenPartialHomeomorph (expChart D)

theorem coordinateChart_coe : (coordinateChart D e : E → G) = coordinateExp D e := by
  funext x
  change expChart D (e.symm x) = exp D (e.symm x)
  rw [expChart_coe]

theorem zero_mem_coordinateChart_source : (0 : E) ∈ (coordinateChart D e).source := by
  change e.symm 0 ∈ (expChart D).source
  simpa only [map_zero] using zero_mem_expChart_source D

theorem one_mem_coordinateChart_target : (1 : G) ∈ (coordinateChart D e).target :=
  one_mem_expChart_target D

/-- Translating the actual identity chart covers the original group. No
smooth transition-map assertion is included in this topological atlas. -/
@[instance_reducible]
noncomputable def coordinateChartedSpace : ChartedSpace E G where
  atlas := Set.range (fun g : G => (Homeomorph.mulLeft g⁻¹).transOpenPartialHomeomorph (coordinateChart D e).symm)
  chartAt g := (Homeomorph.mulLeft g⁻¹).transOpenPartialHomeomorph (coordinateChart D e).symm
  mem_chart_source g := by
    change g⁻¹*g ∈ (coordinateChart D e).target
    simpa only [inv_mul_cancel] using one_mem_coordinateChart_target D e
  chart_mem_atlas g := Set.mem_range_self g

include D in
theorem exists_finite_dimensional_chartedSpace : ∃ d : ℕ,
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin d)) G) := by
  obtain ⟨d,⟨e⟩⟩ := exists_euclidean_equiv D
  exact ⟨d,⟨coordinateChartedSpace D e⟩⟩

/-- Conjugation in these linear coordinates is an actual bounded linear map. -/
noncomputable def coordinateAdjoint (g : G) : E →L[ℝ] E :=
  e.toContinuousLinearMap.comp ((adjoint D g).comp e.symm.toContinuousLinearMap)

theorem coordinateAdjoint_apply (g : G) (x : E) :
    coordinateAdjoint D e g x = e (adjoint D g (e.symm x)) := rfl

theorem coordinateAdjoint_one : coordinateAdjoint D e (1 : G) = 1 := by
  ext x
  simp only [coordinateAdjoint_apply,adjoint_one,ContinuousLinearMap.id_apply,e.apply_symm_apply,
    one_apply_eq_self]

theorem coordinateAdjoint_mul (g h : G) :
    coordinateAdjoint D e (g*h) = coordinateAdjoint D e g*coordinateAdjoint D e h := by
  ext x
  simp only [coordinateAdjoint_apply,adjoint_mul,ContinuousLinearMap.comp_apply,
    mul_apply_eq_comp,e.symm_apply_apply]

theorem coordinateExp_adjoint (g : G) (x : E) :
    coordinateExp D e (coordinateAdjoint D e g x) = g*coordinateExp D e x*g⁻¹ := by
  simp only [coordinateExp,coordinateAdjoint_apply,e.symm_apply_apply,exp_adjoint]

theorem continuous_coordinateAdjoint [FiniteDimensional ℝ E] : Continuous (coordinateAdjoint D e) := by
  apply continuous_clm_apply.mpr
  intro x
  exact e.continuous.comp ((continuous_adjoint_apply D).comp (continuous_id.prodMk continuous_const))

end DirectedCycles.GleasonLieAlgebra
