import DirectedCycles.RoundedPowerEstimates
import DirectedCycles.ContinuousLocalCurveExtension
import DirectedCycles.GleasonOneParameterWindow
import Mathlib.Order.Filter.Ultrafilter.Basic

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [IsTopologicalGroup G]

/-- A compact bound on normalised power segments produces an actual global
continuous one-parameter subgroup. The construction uses a single given
ultrafilter; no Lie structure or differentiable curve is assumed. -/
theorem exists_rounded_power_limit {ι : Type*} (U : Ultrafilter ι)
    (g : ι → G) (N : ι → ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hscale : ∀ᶠ i in (U : Filter ι), 0 < N i ∧ (N i : ℝ)*D.gauge (g i) ≤ R)
    (hzero : Tendsto g (U : Filter ι) (𝓝 (1 : G)))
    (hK : IsCompact {x : G | D.gauge x ≤ 2*R}) :
    ∃ φ : OneParameter G,
      (∀ t : ℝ, D.gauge (φ.eval t) ≤ R*|t|) ∧
      ∀ t : ℝ, |t| ≤ 1 → Tendsto (fun i => roundedPower (g i) (N i) t)
        (U : Filter ι) (𝓝 (φ.eval t)) := by
  let : MetricSpace G := D.compatibleMetric
  let F : ℝ → G := fun t => limUnder (U : Filter ι) (fun i => roundedPower (g i) (N i) t)
  have hν : Tendsto (fun i => D.gauge (g i)) (U : Filter ι) (𝓝 (0 : ℝ)) := by
    simpa only [D.gauge_one,Function.comp_def] using D.continuous_gauge.tendsto 1 |>.comp hzero
  have hgen : ∀ᶠ i in (U : Filter ι), D.gauge (g i) ≤ R := by
    filter_upwards [hscale] with i hi
    have hn : (1 : ℝ) ≤ N i := by exact_mod_cast hi.1
    nlinarith [D.gauge_nonneg (g i)]
  have hnorm : ∀ t : ℝ, ∀ᶠ i in (U : Filter ι),
      D.gauge (roundedPower (g i) (N i) t) ≤ R*|t|+D.gauge (g i) := by
    intro t
    filter_upwards [hscale] with i hi
    have hh := D.roundedPower_gauge (g i) (N i) t
    have hm := mul_le_mul_of_nonneg_right hi.2 (abs_nonneg t)
    nlinarith
  have hconv : ∀ t : ℝ, |t| ≤ 1 →
      Tendsto (fun i => roundedPower (g i) (N i) t) (U : Filter ι) (𝓝 (F t)) := by
    intro t ht
    have hm : ∀ᶠ i in (U : Filter ι), roundedPower (g i) (N i) t ∈ {x : G | D.gauge x ≤ 2*R} := by
      filter_upwards [hnorm t,hgen] with i hi hgi
      nlinarith
    obtain ⟨x,_hx,hx⟩ := hK.ultrafilter_le_nhds' (U.map (fun i => roundedPower (g i) (N i) t)) hm
    exact tendsto_nhds_limUnder ⟨x,hx⟩
  have hF0 : F 0 = 1 := by
    have hh := hconv 0 (by norm_num)
    simp only [roundedPower_zero] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hFgauge : ∀ t : ℝ, |t| ≤ 1 → D.gauge (F t) ≤ R*|t| := by
    intro t ht
    have ha := D.continuous_gauge.tendsto (F t) |>.comp (hconv t ht)
    have hb : Tendsto (fun i => R*|t|+D.gauge (g i)) (U : Filter ι) (𝓝 (R*|t|)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := R*|t|)).add hν
    exact le_of_tendsto_of_tendsto ha hb (hnorm t)
  have hcont0 : ContinuousAt F 0 := by
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    refine ⟨min 1 (ε/(R+1)),lt_min zero_lt_one (div_pos hε (by positivity)),?_⟩
    intro t ht
    have ht' : |t| < min 1 (ε/(R+1)) := by simpa only [Real.dist_eq,sub_zero] using ht
    have ht1 : |t| ≤ 1 := (lt_of_lt_of_le ht' (min_le_left _ _)).le
    have htε := (lt_div_iff₀ (show 0 < R+1 by positivity)).mp (lt_of_lt_of_le ht' (min_le_right _ _))
    rw [hF0,dist_comm]
    change D.gauge (F t) < ε
    nlinarith [hFgauge t ht1,abs_nonneg t]
  have hadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → F (s+t) = F s*F t := by
    intro s t hst
    have hs : |s| ≤ 1 := by linarith [abs_nonneg t]
    have ht : |t| ≤ 1 := by linarith [abs_nonneg s]
    have hsum : |s+t| ≤ 1 := (abs_add_le _ _).trans hst
    have ha := (hconv (s+t) hsum).dist ((hconv s hs).mul (hconv t ht))
    have hb : dist (F (s+t)) (F s*F t) ≤ 0 :=
      le_of_tendsto_of_tendsto ha hν (Filter.Eventually.of_forall fun i => D.roundedPower_add_defect (g i) (N i) s t)
    exact dist_eq_zero.mp (le_antisymm hb dist_nonneg)
  obtain ⟨φ,hφ⟩ := exists_continuous_local_curve_extension F hF0 hcont0 (by norm_num : (0 : ℝ) < 1) hadd
  refine ⟨φ,?_,?_⟩
  · apply D.oneParameter_gauge_global_of_local φ (by norm_num : (0 : ℝ) < 1)
    intro t ht
    rw [hφ t ht]
    exact hFgauge t ht
  · intro t ht
    rw [hφ t ht]
    exact hconv t ht
end GleasonMetricData
end DirectedCycles
