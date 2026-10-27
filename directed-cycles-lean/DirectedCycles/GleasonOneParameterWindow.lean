module

public import DirectedCycles.GleasonOneParameter
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.UniformSpace.CompleteSeparated

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

theorem continuous_gauge : Continuous D.gauge := by
  let : MetricSpace G := D.compatibleMetric
  exact continuous_const.dist continuous_id

def oneParameterWindow (T R : ℝ) : Set (OneParameter G) :=
  {φ | ∀ t : ℝ, |t| ≤ T → D.gauge (φ.eval t) ≤ R}

theorem oneParameterWindow_closed (T R : ℝ) : IsClosed (D.oneParameterWindow T R) := by
  change IsClosed {φ : OneParameter G | ∀ t : ℝ, ∀ _h : |t| ≤ T, D.gauge (φ.eval t) ≤ R}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun t => isClosed_iInter fun _h =>
    isClosed_le (D.continuous_gauge.comp (continuous_eval_const (Multiplicative.ofAdd t))) continuous_const

/-- Every actual one-parameter subgroup enters each positive metric window
on some closed interval about zero. -/
theorem oneParameter_exists_window (φ : OneParameter G) {R : ℝ} (hR : 0 < R) :
    ∃ T : ℝ, 0 < T ∧ φ ∈ D.oneParameterWindow T R := by
  have hc := (D.continuous_gauge.comp φ.continuous_eval).continuousAt (x := 0)
  have hn : {t : ℝ | D.gauge (φ.eval t) < R} ∈ 𝓝 (0 : ℝ) := by
    change (D.gauge ∘ φ.eval) ⁻¹' Set.Iio R ∈ 𝓝 (0 : ℝ)
    apply hc.preimage_mem_nhds
    apply Iio_mem_nhds
    simpa only [Function.comp_apply,φ.eval_zero,D.gauge_one] using hR
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ/2,by positivity,?_⟩
  intro t ht
  have htb : t ∈ Metric.ball (0 : ℝ) δ := by
    change |t-0| < δ
    rw [sub_zero]
    linarith
  exact (hball htb).le

/-- The interval window has a common global modulus of continuity. -/
theorem oneParameterWindow_equicontinuous {T R : ℝ}
    (hT : 0 < T) (hR : 0 ≤ R) (hscale : (D.constant+1)*R ≤ 1/D.constant) :
    let := D.compatibleMetric
    Equicontinuous (fun φ : D.oneParameterWindow T R => (φ.val : Multiplicative ℝ → G)) := by
  let : MetricSpace G := D.compatibleMetric
  let L : ℝ := 2*D.constant*R/T
  apply Metric.equicontinuous_of_continuity_modulus (fun x => L*x)
    (by simpa using (tendsto_const_nhds.mul tendsto_id : Tendsto (fun x : ℝ => L*x) (𝓝 0) (𝓝 (L*0))))
  intro x y φ
  change D.metric.dist (φ.val.eval x.toAdd) (φ.val.eval y.toAdd) ≤ L*|x.toAdd-y.toAdd|
  rw [abs_sub_comm]
  exact D.oneParameter_dist_bound φ.val hT hR hscale φ.property _ _

/-- Each fixed evaluation of the interval window lies in an actual compact
power image of the small closed ball. -/
theorem oneParameterWindow_pointwise_compact [IsTopologicalGroup G] {T R : ℝ}
    (hT : 0 < T)
    (hK : IsCompact {g : G | D.gauge g ≤ R}) (x : Multiplicative ℝ) :
    ∃ Q : Set G, IsCompact Q ∧ ∀ φ ∈ D.oneParameterWindow T R, φ x ∈ Q := by
  obtain ⟨m,hm⟩ := exists_nat_gt (|x.toAdd|/T)
  have hmpos : (0 : ℝ) < m := lt_of_le_of_lt (div_nonneg (abs_nonneg _) hT.le) hm
  refine ⟨(fun g : G => g^m) '' {g : G | D.gauge g ≤ R},hK.image (continuous_pow m),?_⟩
  intro φ hφ
  refine ⟨φ.eval (x.toAdd/(m : ℝ)),?_,?_⟩
  · apply hφ
    rw [abs_div,abs_of_pos hmpos]
    apply (div_le_iff₀ hmpos).mpr
    nlinarith [(div_lt_iff₀ hT).mp hm]
  · change (φ.eval (x.toAdd/(m : ℝ)))^m = φ x
    rw [← φ.eval_nat_mul,mul_div_cancel₀ _ (ne_of_gt hmpos)]
    rfl

/-- Arzela-Ascoli applies to the actual compact-open space of continuous
homomorphisms, whose algebraic relations define a closed subspace. -/
theorem oneParameterWindow_compact [IsTopologicalGroup G] [LocallyCompactSpace G]
    {T R : ℝ} (hT : 0 < T) (hR : 0 ≤ R)
    (hscale : (D.constant+1)*R ≤ 1/D.constant)
    (hK : IsCompact {g : G | D.gauge g ≤ R}) :
    IsCompact (D.oneParameterWindow T R) := by
  let : MetricSpace G := D.compatibleMetric
  have hc : IsClosedEmbedding
      (ContinuousMap.toUniformOnFunIsCompact : C(Multiplicative ℝ,G) →
        UniformOnFun (Multiplicative ℝ) G {K | IsCompact K}) :=
    ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding,by
      rw [ContinuousMap.range_toUniformOnFunIsCompact]
      exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith⟩
  have hf := hc.comp (ContinuousMonoidHom.isClosedEmbedding_toContinuousMap (Multiplicative ℝ) G)
  have he := D.oneParameterWindow_equicontinuous hT hR hscale
  have h := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (fun _ h => h) hf
    (fun K _hK => he.equicontinuousOn K)
    (fun _K _hK x _hx => D.oneParameterWindow_pointwise_compact hT hK x)
  simpa only [(D.oneParameterWindow_closed T R).closure_eq] using h
end GleasonMetricData
end DirectedCycles
