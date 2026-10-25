module

public import DirectedCycles.ParameterIntegralCurveBounds
public import DirectedCycles.OperatorFieldDifference
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The endpoint of a Lipschitz parameter family of actual integral curves is
strictly differentiable at the zero parameter. This two-point estimate is the
regularity needed by the inverse function theorem. -/
theorem parameter_integral_endpoint_strict_derivative (A : E → E →L[ℝ] E)
    (hA : ContDiffAt ℝ 1 A 0) (hA0 : A 0 = ContinuousLinearMap.id ℝ E)
    (f : E × ℝ → E) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (K : NNReal)
    (hder : ∀ v : E, ‖v‖ ≤ r → f (v,0) = 0 ∧ ∀ t : ℝ, |t| < ε →
      HasDerivAt (fun t => f (v,t)) (A (f (v,t)) v) t)
    (hLip : ∀ t : ℝ, |t| < ε → LipschitzOnWith K (fun v => f (v,t)) (Metric.closedBall 0 r))
    {τ : ℝ} (hτ : 0 < τ) (hτε : τ < ε) :
    HasStrictFDerivAt (fun v => f (v,τ)) (τ • ContinuousLinearMap.id ℝ E) 0 := by
  obtain ⟨_,hsize⟩ := parameter_integral_curve_norm_bound A f hr.le hε K hder hLip
  obtain ⟨J,S,hS,hALip⟩ := hA.exists_lipschitzOnWith
  rw [hasStrictFDerivAt_iff_isLittleO]
  apply Asymptotics.isLittleO_iff.2
  intro c hc
  let η := c/(2*τ)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hnearA : ∀ᶠ x : E in 𝓝 0, x ∈ S ∧ ‖A x-ContinuousLinearMap.id ℝ E‖ < η := by
    have hn : ContinuousAt (fun x => ‖A x-ContinuousLinearMap.id ℝ E‖) 0 :=
      (hA.continuousAt.sub continuousAt_const).norm
    have hb : ∀ᶠ x : E in 𝓝 0, ‖A x-ContinuousLinearMap.id ℝ E‖ < η :=
      hn.preimage_mem_nhds (Iio_mem_nhds (by simpa only [hA0,sub_self,norm_zero] using hη))
    exact Filter.Eventually.and hS hb
  obtain ⟨a,ha,hsmallA⟩ := Metric.mem_nhds_iff.mp hnearA
  let δ := min r (min (a/((K : ℝ)+1)) (η/((J : ℝ)*K+1)))
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min hr (lt_min (by positivity) (by positivity))
  have hcontrol : ∀ v : E, ‖v‖ < δ → ‖v‖ ≤ r ∧ (J : ℝ)*K*‖v‖ ≤ η ∧
      ∀ t : ℝ, |t| < ε → f (v,t) ∈ S ∧ ‖A (f (v,t))-ContinuousLinearMap.id ℝ E‖ ≤ η := by
    intro v hv
    have hvr : ‖v‖ ≤ r := (hv.trans_le (min_le_left _ _)).le
    have hva : ‖v‖ < a/((K : ℝ)+1) := hv.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hvη : ‖v‖ < η/((J : ℝ)*K+1) := hv.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hKa := (lt_div_iff₀ (show (0 : ℝ) < K+1 by positivity)).1 hva
    have hJη := (lt_div_iff₀ (show (0 : ℝ) < J*K+1 by positivity)).1 hvη
    refine ⟨hvr,by nlinarith [norm_nonneg v],?_⟩
    intro t ht
    have hnorm : ‖f (v,t)‖ < a := lt_of_le_of_lt (hsize v hvr t ht) (by nlinarith [norm_nonneg v])
    obtain ⟨hmem,hbound⟩ := hsmallA (show f (v,t) ∈ Metric.ball 0 a from by simpa only [Metric.mem_ball,dist_zero_right] using hnorm)
    exact ⟨hmem,hbound.le⟩
  have hnear : ∀ᶠ p : E × E in 𝓝 (0,0), ‖p.1‖ < δ ∧ ‖p.2‖ < δ := by
    have hf : Filter.Tendsto (fun p : E × E => p.1) (𝓝 (0,0)) (𝓝 0) := continuousAt_fst
    have hs : Filter.Tendsto (fun p : E × E => p.2) (𝓝 (0,0)) (𝓝 0) := continuousAt_snd
    filter_upwards [hf.eventually (Metric.ball_mem_nhds (0 : E) hδ),hs.eventually (Metric.ball_mem_nhds (0 : E) hδ)] with p hp hq
    exact ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hp,by simpa only [Metric.mem_ball,dist_zero_right] using hq⟩
  filter_upwards [hnear] with p hp
  obtain ⟨hv,hvη,hvc⟩ := hcontrol p.1 hp.1
  obtain ⟨hw,hwη,hwc⟩ := hcontrol p.2 hp.2
  let g : ℝ → E := fun t => f (p.1,t)-f (p.2,t)-t • (p.1-p.2)
  let g' : ℝ → E := fun t => A (f (p.1,t)) p.1-A (f (p.2,t)) p.2-(p.1-p.2)
  have htε : ∀ t ∈ Set.Icc 0 τ, |t| < ε := by
    intro t ht
    rw [abs_of_nonneg ht.1]
    exact ht.2.trans_lt hτε
  have hgder : ∀ t ∈ Set.Icc 0 τ, HasDerivAt g (g' t) t := by
    intro t ht
    exact (((hder p.1 hv).2 t (htε t ht)).sub ((hder p.2 hw).2 t (htε t ht))).sub
      (by simpa only [id_eq,one_smul] using (hasDerivAt_id t).smul_const (p.1-p.2))
  have hbound : ∀ t ∈ Set.Ico 0 τ, ‖g' t‖ ≤ 2*η*‖p.1-p.2‖ := by
    intro t ht
    have hte := htε t (Set.Ico_subset_Icc_self ht)
    have hfield := hALip.dist_le_mul (f (p.1,t)) (hvc t hte).1 (f (p.2,t)) (hwc t hte).1
    have hparam := (hLip t hte).dist_le_mul p.1
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hv) p.2
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hw)
    have hAB : ‖A (f (p.1,t))-A (f (p.2,t))‖ ≤ ((J : ℝ)*K)*‖p.1-p.2‖ := by
      rw [dist_eq_norm,dist_eq_norm] at hfield
      rw [dist_eq_norm,dist_eq_norm] at hparam
      calc
        _ ≤ (J : ℝ)*‖f (p.1,t)-f (p.2,t)‖ := hfield
        _ ≤ (J : ℝ)*((K : ℝ)*‖p.1-p.2‖) := mul_le_mul_of_nonneg_left hparam J.coe_nonneg
        _ = _ := by ring
    exact operator_field_difference_bound _ _ p.1 p.2 (hvc t hte).2 hAB hwη
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hgder t ht).hasDerivWithinAt) hbound τ (show τ ∈ Set.Icc 0 τ from ⟨hτ.le,le_rfl⟩)
  have hg0 : g 0 = 0 := by simp only [g,(hder p.1 hv).1,(hder p.2 hw).1,zero_smul,sub_self]
  rw [hg0,sub_zero,sub_zero] at hh
  change ‖f (p.1,τ)-f (p.2,τ)-(τ • ContinuousLinearMap.id ℝ E) (p.1-p.2)‖ ≤ c*‖p.1-p.2‖
  simpa only [g,smul_apply,ContinuousLinearMap.id_apply,
    show 2*η*‖p.1-p.2‖*τ = c*‖p.1-p.2‖ by dsimp only [η]; field_simp] using hh
end DirectedCycles
