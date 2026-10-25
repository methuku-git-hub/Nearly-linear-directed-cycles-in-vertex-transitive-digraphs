module

public import DirectedCycles.GleasonSmoothAtlas
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology ContDiff Manifold
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- Global multiplication is smooth in the translated restricted charts.
At an arbitrary pair its coordinate formula is the already proved smooth
identity product composed with an actual linear adjoint map. -/
theorem restrictedCoordinates_contMDiff_mul (r : ℝ) (hr : 0 < r) :
    let := restrictedCoordinateChartedSpace D e r hr
    ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ (fun p : G × G => p.1*p.2) := by
  let := restrictedCoordinateChartedSpace D e r hr
  have hchart (a b : G) : extChartAt 𝓘(ℝ,E) a b = coordinateLog D e (a⁻¹*b) := rfl
  have hinv (a : G) (x : E) : (extChartAt 𝓘(ℝ,E) a).symm x = a*coordinateExp D e x := by
    change (translatedRestrictedChart D e r a).symm x = _
    exact translatedRestrictedChart_symm_apply D e r a x
  change ∀ p : G × G, ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ (fun q : G × G => q.1*q.2) p
  intro p
  rw [contMDiffAt_iff]
  refine ⟨continuous_mul.continuousAt,?_⟩
  have hpoint : extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) p p = (0 : E × E) := by
    rw [extChartAt_prod]
    change (extChartAt 𝓘(ℝ,E) p.1 p.1,extChartAt 𝓘(ℝ,E) p.2 p.2) = _
    simp only [hchart,inv_mul_cancel,coordinateLog_one,Prod.mk_zero_zero]
  rw [hpoint]
  have he : (extChartAt 𝓘(ℝ,E) (p.1*p.2) ∘ (fun q : G × G => q.1*q.2) ∘
      (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) p).symm) =
      (fun q : E × E => coordinateMul D e (coordinateAdjoint D e p.2⁻¹ q.1,q.2)) := by
    funext q
    rw [extChartAt_prod]
    change coordinateLog D e ((p.1*p.2)⁻¹*((extChartAt 𝓘(ℝ,E) p.1).symm q.1*(extChartAt 𝓘(ℝ,E) p.2).symm q.2)) = _
    rw [hinv,hinv]
    dsimp only [coordinateMul]
    rw [coordinateExp_adjoint]
    congr 1
    group
  rw [he]
  let T : E × E →L[ℝ] E × E :=
    ((coordinateAdjoint D e p.2⁻¹).comp (ContinuousLinearMap.fst ℝ E E)).prod (ContinuousLinearMap.snd ℝ E E)
  have hc : ContDiffAt ℝ ∞ (coordinateMul D e) (T 0) := by
    simpa only [map_zero,Prod.mk_zero_zero] using coordinateMul_contDiffAt_zero D e
  exact (hc.comp (0 : E × E) T.contDiff.contDiffAt).contDiffWithinAt

omit [FiniteDimensional ℝ E] in
/-- Global inversion has a linear coordinate germ at every point, given
by negation followed by the actual adjoint action. -/
theorem restrictedCoordinates_contMDiff_inv (r : ℝ) (hr : 0 < r) :
    let := restrictedCoordinateChartedSpace D e r hr
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun g : G => g⁻¹) := by
  let := restrictedCoordinateChartedSpace D e r hr
  have hchart (a b : G) : extChartAt 𝓘(ℝ,E) a b = coordinateLog D e (a⁻¹*b) := rfl
  have hinv (a : G) (x : E) : (extChartAt 𝓘(ℝ,E) a).symm x = a*coordinateExp D e x := by
    change (translatedRestrictedChart D e r a).symm x = _
    exact translatedRestrictedChart_symm_apply D e r a x
  change ∀ g : G, ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun h : G => h⁻¹) g
  intro g
  rw [contMDiffAt_iff]
  refine ⟨continuous_inv.continuousAt,?_⟩
  have hpoint : extChartAt 𝓘(ℝ,E) g g = 0 := by rw [hchart,inv_mul_cancel,coordinateLog_one]
  rw [hpoint]
  let T : E →L[ℝ] E := -(coordinateAdjoint D e g)
  have hT0 : T (0 : E) = 0 := map_zero _
  have hs : ∀ᶠ x : E in 𝓝 0, T x ∈ (coordinateChart D e).source := by
    have hc : Tendsto T (𝓝 0) (𝓝 0) := by simpa only [hT0] using T.continuous.tendsto 0
    exact hc.eventually ((coordinateChart D e).open_source.mem_nhds (zero_mem_coordinateChart_source D e))
  have he : (extChartAt 𝓘(ℝ,E) g⁻¹ ∘ (fun h : G => h⁻¹) ∘ (extChartAt 𝓘(ℝ,E) g).symm) =ᶠ[𝓝 0] T := by
    filter_upwards [hs] with x hx
    change coordinateLog D e ((g⁻¹)⁻¹*((extChartAt 𝓘(ℝ,E) g).symm x)⁻¹) = T x
    rw [inv_inv,hinv]
    have hTx : T x = coordinateAdjoint D e g (-x) := by simp [T]
    have heq : g*(g*coordinateExp D e x)⁻¹ = coordinateExp D e (T x) := by
      rw [hTx,coordinateExp_adjoint,coordinateExp_neg]
      group
    rw [heq]
    exact coordinateLog_exp D e hx
  exact (T.contDiff.contDiffAt.congr_of_eventuallyEq he).contDiffWithinAt

end DirectedCycles.GleasonLieAlgebra
