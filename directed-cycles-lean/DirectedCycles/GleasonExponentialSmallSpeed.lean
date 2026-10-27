module

public import DirectedCycles.GleasonExponentialMap
public import Mathlib.Order.Filter.Ultrafilter.Basic

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace GleasonLieAlgebra
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [IsTopologicalGroup G] [LocallyCompactSpace G]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
/-- Convergence to zero in the actual curve space implies eventually
arbitrarily small global speed bounds. -/
theorem eventually_small_speed {ι : Type*} {l : Filter ι} {x : ι → GleasonLieAlgebra D}
    (hx : Tendsto x l (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ t : ℝ, D.gauge ((toOneParameter D (x i)).eval t) ≤ ε*|t| := by
  have hC := D.constant_pos
  let R := min (1/(D.constant*(D.constant+1))) (ε/(2*D.constant))
  have hR : 0 < R := by dsimp [R]; positivity
  have hscale : (D.constant+1)*R ≤ 1/D.constant := by
    have h := mul_le_mul_of_nonneg_left (min_le_left (1/(D.constant*(D.constant+1))) (ε/(2*D.constant))) (by linarith : 0 ≤ D.constant+1)
    apply h.trans_eq
    field_simp
  have hspeed : 2*D.constant*R ≤ ε := by
    have h := (le_div_iff₀ (show 0 < 2*D.constant by positivity)).mp (min_le_right (1/(D.constant*(D.constant+1))) (ε/(2*D.constant)))
    nlinarith
  have hU : D.oneParameterWindow 1 R ∈ 𝓝 (1 : OneParameter G) := by
    apply D.oneParameterWindow_mem_nhds
    intro t _ht
    change D.gauge (1 : G) < R
    simpa only [D.gauge_one] using hR
  have hh : Tendsto (fun i => toOneParameter D (x i)) l (𝓝 (1 : OneParameter G)) :=
    (toOneParameter D).continuous.tendsto 0 |>.comp hx
  filter_upwards [hh.eventually hU] with i hi
  intro t
  have hb := D.oneParameter_gauge_bound (toOneParameter D (x i)) (by norm_num : (0 : ℝ) < 1) hR.le hscale hi t
  simp only [div_one] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hspeed (abs_nonneg t))

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
/-- Compactness and local injectivity recover convergence of the actual
vector parameters from convergence of their evaluated group elements. -/
theorem compact_exp_lift_tendsto_zero {ι : Type*} (U : Ultrafilter ι)
    {K : Set (GleasonLieAlgebra D)} (hK : IsCompact K) (hK0 : (0 : GleasonLieAlgebra D) ∈ K)
    (hinj : Set.InjOn (exp D) K) (x : ι → GleasonLieAlgebra D)
    (hx : ∀ᶠ i in (U : Filter ι), x i ∈ K)
    (he : Tendsto (fun i => exp D (x i)) (U : Filter ι) (𝓝 (1 : G))) :
    Tendsto x (U : Filter ι) (𝓝 0) := by
  let : MetricSpace G := D.compatibleMetric
  obtain ⟨y,hy,hlim⟩ := hK.ultrafilter_le_nhds' (U.map x) hx
  have hye : exp D y = 1 := tendsto_nhds_unique ((continuous_exp D).tendsto y |>.comp hlim) he
  have hy0 : y = 0 := hinj hy hK0 (hye.trans (exp_zero D).symm)
  change Tendsto x (U : Filter ι) (𝓝 y) at hlim
  simpa only [hy0] using hlim
end GleasonLieAlgebra
end DirectedCycles
