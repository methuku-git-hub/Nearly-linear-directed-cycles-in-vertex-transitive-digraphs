module

public import DirectedCycles.GleasonTrotterRefinement
public import DirectedCycles.CommonMultipleCauchy
public import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace OneParameter
variable {G : Type*} [Group G] [TopologicalSpace G]
/-- The limit selector for the actual product sequence. Convergence is
proved on the small interval where this selector is used. -/
noncomputable def productLimit (φ ψ : OneParameter G) (t : ℝ) : G :=
  limUnder atTop (φ.productApprox ψ t)
end OneParameter
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    {r : ℝ}
    (hpow : ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r →
      (n : ℝ)*D.gauge h ≤ r → D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h)
    (hr : r ≤ 1/(8*D.constant))
    (φ ψ : OneParameter G) {L₁ L₂ : ℝ} (hL₁ : 0 ≤ L₁)
    (hφ : ∀ t : ℝ, D.gauge (φ.eval t) ≤ L₁*|t|)
    (hψ : ∀ t : ℝ, D.gauge (ψ.eval t) ≤ L₂*|t|)

include hpow hr hL₁ hφ hψ

/-- The product sequence actually converges in the original group topology. -/
theorem productLimit_tendsto (t : ℝ) (ht : (L₁+L₂)*|t| ≤ r) :
    Tendsto (φ.productApprox ψ t) atTop (𝓝 (φ.productLimit ψ t)) := by
  let : MetricSpace G := D.compatibleMetric
  let : CompleteSpace G := D.compatibleMetric_complete
  have h := D.productApprox_refinement hpow hr φ ψ hL₁ hφ hψ t ht
  exact (cauchySeq_of_common_multiple _ (4*D.constant*L₁*L₂*|t|^2) h).tendsto_limUnder

/-- The limit retains the explicit inverse-subdivision error bound. -/
theorem productLimit_distance (t : ℝ) (ht : (L₁+L₂)*|t| ≤ r) (n : ℕ) (hn : 0 < n) :
    D.metric.dist (φ.productApprox ψ t n) (φ.productLimit ψ t) ≤
      (4*D.constant*L₁*L₂*|t|^2)/(n : ℝ) := by
  let : MetricSpace G := D.compatibleMetric
  exact dist_limit_le_of_common_multiple
    (D.productLimit_tendsto hpow hr φ ψ hL₁ hφ hψ t ht)
    (D.productApprox_refinement hpow hr φ ψ hL₁ hφ hψ t ht) n hn

/-- A limit of the small product approximations has the same linear gauge bound. -/
theorem productLimit_gauge (t : ℝ) (ht : (L₁+L₂)*|t| ≤ r) :
    D.gauge (φ.productLimit ψ t) ≤ (L₁+L₂)*|t| := by
  let : MetricSpace G := D.compatibleMetric
  have hg : Continuous D.gauge := continuous_const.dist continuous_id
  have hh := hg.tendsto _ |>.comp (D.productLimit_tendsto hpow hr φ ψ hL₁ hφ hψ t ht)
  apply le_of_tendsto hh
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact D.productApprox_gauge φ ψ hφ hψ t n (by omega)

/-- Convergence is uniform on a whole small parameter interval, with a
quantitative error independent of the parameter. -/
theorem productLimit_uniform (hL₂ : 0 ≤ L₂) {T : ℝ}
    (hT : 0 ≤ T) (hsmall : (L₁+L₂)*T ≤ r) :
    let := D.compatibleMetric
    TendstoUniformlyOn (fun n t => φ.productApprox ψ t n) (φ.productLimit ψ)
      atTop {t : ℝ | |t| ≤ T} := by
  let : MetricSpace G := D.compatibleMetric
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let K : ℝ := 4*D.constant*L₁*L₂*T^2
  have hev : ∀ᶠ n : ℕ in atTop, K/(n : ℝ) < ε :=
    (tendsto_const_div_atTop_nhds_zero_nat K).eventually (gt_mem_nhds hε)
  filter_upwards [hev,eventually_ge_atTop 1] with n hn hn1
  intro t ht
  have htr : (L₁+L₂)*|t| ≤ r :=
    (mul_le_mul_of_nonneg_left ht (add_nonneg hL₁ hL₂)).trans hsmall
  have hd := D.productLimit_distance hpow hr φ ψ hL₁ hφ hψ t htr n (by omega)
  have ht2 : |t|^2 ≤ T^2 := by nlinarith [abs_nonneg t]
  have hC := D.constant_pos
  have hcoef : 0 ≤ 4*D.constant*L₁*L₂ := by positivity
  have hK : 4*D.constant*L₁*L₂*|t|^2 ≤ K := mul_le_mul_of_nonneg_left ht2 hcoef
  have hdiv := div_le_div_of_nonneg_right hK (Nat.cast_nonneg n)
  change D.metric.dist (φ.productLimit ψ t) (φ.productApprox ψ t n) < ε
  rw [D.metric.dist_comm]
  exact (hd.trans hdiv).trans_lt hn

/-- The constructed limit is continuous on the small parameter interval. -/
theorem productLimit_continuousOn (hL₂ : 0 ≤ L₂) {T : ℝ}
    (hT : 0 ≤ T) (hsmall : (L₁+L₂)*T ≤ r) :
    ContinuousOn (φ.productLimit ψ) {t : ℝ | |t| ≤ T} := by
  let : MetricSpace G := D.compatibleMetric
  apply (D.productLimit_uniform hpow hr φ ψ hL₁ hφ hψ hL₂ hT hsmall).continuousOn
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro n
  exact (((φ.continuous_eval.comp (continuous_id.div_const (n : ℝ))).mul
    (ψ.continuous_eval.comp (continuous_id.div_const (n : ℝ)))).pow n).continuousOn
end GleasonMetricData
end DirectedCycles
