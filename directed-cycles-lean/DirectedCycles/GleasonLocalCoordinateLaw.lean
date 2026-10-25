module

public import DirectedCycles.GleasonCoordinateProductError

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : GleasonLieAlgebra D ≃L[ℝ] E)

noncomputable def coordinateLog : G → E := (coordinateChart D e).symm

theorem coordinateLog_exp {x : E} (hx : x ∈ (coordinateChart D e).source) :
    coordinateLog D e (coordinateExp D e x) = x := by
  rw [← coordinateChart_coe]
  exact (coordinateChart D e).left_inv hx

theorem coordinateExp_log {g : G} (hg : g ∈ (coordinateChart D e).target) :
    coordinateExp D e (coordinateLog D e g) = g := by
  rw [← coordinateChart_coe]
  exact (coordinateChart D e).right_inv hg

@[simp] theorem coordinateLog_one : coordinateLog D e (1 : G) = 0 := by
  have h := coordinateLog_exp D e (zero_mem_coordinateChart_source D e)
  simpa only [coordinateExp_zero] using h

theorem coordinateLog_continuousAt_one : ContinuousAt (coordinateLog D e) (1 : G) :=
  (coordinateChart D e).symm.continuousAt (one_mem_coordinateChart_target D e)

/-- The actual local group product transported through the constructed
chart, written as a total function for use in local analytic statements. -/
noncomputable def coordinateMul (p : E × E) : E :=
  coordinateLog D e (coordinateExp D e p.1*coordinateExp D e p.2)

@[simp] theorem coordinateMul_zero : coordinateMul D e (0,0) = 0 := by
  simp only [coordinateMul,coordinateExp_zero,one_mul,coordinateLog_one]

theorem coordinateMul_continuousAt_zero : ContinuousAt (coordinateMul D e) (0,0) := by
  have h : Continuous (fun p : E × E => coordinateExp D e p.1*coordinateExp D e p.2) :=
    ((continuous_coordinateExp D e).comp continuous_fst).mul ((continuous_coordinateExp D e).comp continuous_snd)
  exact (coordinateLog_continuousAt_one D e).comp_of_eq h.continuousAt (by simp)

theorem coordinateMul_identity_axes :
    (fun x => coordinateMul D e (x,0)) =ᶠ[𝓝 (0 : E)] id ∧
    (fun x => coordinateMul D e (0,x)) =ᶠ[𝓝 (0 : E)] id := by
  have hS : (coordinateChart D e).source ∈ 𝓝 (0 : E) :=
    (coordinateChart D e).open_source.mem_nhds (zero_mem_coordinateChart_source D e)
  constructor
  · filter_upwards [hS] with x hx
    simp only [coordinateMul,coordinateExp_zero,mul_one]
    exact coordinateLog_exp D e hx
  · filter_upwards [hS] with x hx
    simp only [coordinateMul,coordinateExp_zero,one_mul]
    exact coordinateLog_exp D e hx

/-- Along every radial line the transported local product is exactly
scalar addition whenever the resulting point belongs to the chart. -/
theorem coordinateMul_radial (s t : ℝ) (x : E)
    (h : (s+t) • x ∈ (coordinateChart D e).source) :
    coordinateMul D e (s • x,t • x) = (s+t) • x := by
  dsimp only [coordinateMul]
  rw [coordinateExp_smul,coordinateExp_smul,← OneParameter.eval_add,← coordinateExp_smul]
  exact coordinateLog_exp D e h

/-- The chart evaluates the transported product to the actual group
product whenever that product is in the chart target. -/
theorem coordinateExp_mul {x y : E}
    (h : coordinateExp D e x*coordinateExp D e y ∈ (coordinateChart D e).target) :
    coordinateExp D e (coordinateMul D e (x,y)) = coordinateExp D e x*coordinateExp D e y :=
  coordinateExp_log D e h

end DirectedCycles.GleasonLieAlgebra
