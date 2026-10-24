import DirectedCycles.GleasonTranslationDerivative

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- The left increment of a product, expressed using the actual adjoint
and the two actual left differences. -/
noncomputable def coordinateProductIncrement (x y : E) (p : E × E) : E :=
  coordinateMul D e (coordinateAdjoint D e ((coordinateExp D e y)⁻¹)
    (coordinateLeftDifference D e x p.1),coordinateLeftDifference D e y p.2)

@[simp] theorem coordinateProductIncrement_self (x y : E) :
    coordinateProductIncrement D e x y (x,y) = 0 := by
  simp only [coordinateProductIncrement,coordinateLeftDifference_self,map_zero,coordinateMul_zero]

theorem coordinateProductIncrement_pair_continuousAt (x y : E) :
    ContinuousAt (fun p : E × E =>
      (coordinateAdjoint D e ((coordinateExp D e y)⁻¹) (coordinateLeftDifference D e x p.1),
       coordinateLeftDifference D e y p.2)) (x,y) := by
  have hx := (coordinateLeftDifference_continuousAt D e x).comp_of_eq (continuous_fst.continuousAt (x := (x,y))) rfl
  have hy := (coordinateLeftDifference_continuousAt D e y).comp_of_eq (continuous_snd.continuousAt (x := (x,y))) rfl
  exact ((coordinateAdjoint D e _).continuous.continuousAt.comp hx).prodMk hy

theorem coordinateProductIncrement_continuousAt (x y : E) :
    ContinuousAt (coordinateProductIncrement D e x y) (x,y) := by
  exact (coordinateMul_continuousAt_zero D e).comp_of_eq
    (coordinateProductIncrement_pair_continuousAt D e x y) (by simp)

theorem coordinateLeftDifference_eventually_target (x : E) :
    ∀ᶠ y : E in 𝓝 x, (coordinateExp D e x)⁻¹*coordinateExp D e y ∈ (coordinateChart D e).target := by
  have hc : Continuous (fun y : E => (coordinateExp D e x)⁻¹*coordinateExp D e y) :=
    continuous_const.mul (continuous_coordinateExp D e)
  have ht : Tendsto (fun y : E => (coordinateExp D e x)⁻¹*coordinateExp D e y) (𝓝 x) (𝓝 1) := by
    simpa only [inv_mul_cancel] using hc.tendsto x
  exact ht.eventually ((coordinateChart D e).open_target.mem_nhds (one_mem_coordinateChart_target D e))

/-- Exact factorization of the product in coordinates wherever the
three intervening logarithms are evaluated in their genuine domains. -/
theorem coordinateMul_increment_factorization {x y : E} {p : E × E}
    (hbase : coordinateExp D e x*coordinateExp D e y ∈ (coordinateChart D e).target)
    (hx : (coordinateExp D e x)⁻¹*coordinateExp D e p.1 ∈ (coordinateChart D e).target)
    (hy : (coordinateExp D e y)⁻¹*coordinateExp D e p.2 ∈ (coordinateChart D e).target)
    (hi : coordinateExp D e (coordinateAdjoint D e ((coordinateExp D e y)⁻¹)
        (coordinateLeftDifference D e x p.1))*coordinateExp D e (coordinateLeftDifference D e y p.2)
      ∈ (coordinateChart D e).target) :
    coordinateMul D e p = coordinateMul D e (coordinateMul D e (x,y),coordinateProductIncrement D e x y p) := by
  have hei : coordinateExp D e (coordinateProductIncrement D e x y p) =
      coordinateExp D e (coordinateAdjoint D e ((coordinateExp D e y)⁻¹)
        (coordinateLeftDifference D e x p.1))*coordinateExp D e (coordinateLeftDifference D e y p.2) :=
    coordinateExp_mul D e hi
  change coordinateLog D e (coordinateExp D e p.1*coordinateExp D e p.2) =
    coordinateLog D e (coordinateExp D e (coordinateMul D e (x,y))*coordinateExp D e (coordinateProductIncrement D e x y p))
  rw [coordinateExp_mul D e hbase,hei,coordinateExp_adjoint]
  simp only [coordinateLeftDifference]
  rw [coordinateExp_log D e hx,coordinateExp_log D e hy]
  congr 1
  group

/-- The exact factorization holds on a neighbourhood of each genuine
base product. -/
theorem coordinateMul_increment_eventuallyEq {x y : E}
    (hbase : coordinateExp D e x*coordinateExp D e y ∈ (coordinateChart D e).target) :
    (coordinateMul D e) =ᶠ[𝓝 (x,y)]
      (fun p => coordinateMul D e (coordinateMul D e (x,y),coordinateProductIncrement D e x y p)) := by
  have hx := (continuous_fst.continuousAt (x := (x,y))).eventually (coordinateLeftDifference_eventually_target D e x)
  have hy := (continuous_snd.continuousAt (x := (x,y))).eventually (coordinateLeftDifference_eventually_target D e y)
  have hc : Continuous (fun q : E × E => coordinateExp D e q.1*coordinateExp D e q.2) :=
    ((continuous_coordinateExp D e).comp continuous_fst).mul ((continuous_coordinateExp D e).comp continuous_snd)
  have ht : Tendsto (fun p : E × E =>
      coordinateExp D e (coordinateAdjoint D e ((coordinateExp D e y)⁻¹) (coordinateLeftDifference D e x p.1))*
        coordinateExp D e (coordinateLeftDifference D e y p.2)) (𝓝 (x,y)) (𝓝 1) := by
    have hh := hc.continuousAt.comp (coordinateProductIncrement_pair_continuousAt D e x y)
    simpa only [ContinuousAt,Function.comp_def,coordinateLeftDifference_self,map_zero,coordinateExp_zero,one_mul] using hh
  have hi := ht.eventually ((coordinateChart D e).open_target.mem_nhds (one_mem_coordinateChart_target D e))
  filter_upwards [hx,hy,hi] with p hx' hy' hi'
  exact coordinateMul_increment_factorization D e hbase hx' hy' hi'

end DirectedCycles.GleasonLieAlgebra
