module

public import DirectedCycles.SmoothLocalIntegralCurve
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A smooth operator field admits a jointly continuous family of actual
integral curves, with the tangent as a parameter. The parameter is a constant
component of an augmented ODE, so it is not an assumed smooth flow. -/
theorem exists_continuous_parameter_integral_curves (A : E → E →L[ℝ] E)
    (hA : ContDiffAt ℝ 1 A 0) :
    ∃ f : E × ℝ → E, ContinuousAt f (0,0) ∧
      (∃ D : Set (E × ℝ), IsOpen D ∧ (0,0) ∈ D ∧ ContinuousOn f D) ∧
      (∀ᶠ v : E in 𝓝 0, f (v,0) = 0) ∧
      ∀ᶠ p : E × ℝ in 𝓝 (0,0), HasDerivAt (fun t => f (p.1,t)) (A (f p) p.1) p.2 := by
  let V : E × E → E × E := fun p => (0,A p.2 p.1)
  have hV : ContDiffAt ℝ 1 V (0,0) := contDiffAt_const.prodMk
    ((hA.comp (0,0) contDiffAt_snd).clm_apply contDiffAt_fst)
  obtain ⟨ε,hε,a,r,B,K,hr,hpl⟩ := IsPicardLindelof.of_contDiffAt_one hV
  obtain ⟨α,hα,hαcont⟩ := (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hz : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by constructor <;> linarith
  have hα' : ∀ v : E, ‖v‖ ≤ (r : ℝ) → α ((v,0),0) = (v,0) ∧
      ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt (fun t => α ((v,0),t)) (V (α ((v,0),t))) t := by
    intro v hv
    have hvr : (v,(0 : E)) ∈ Metric.closedBall (0,0) (r : ℝ) := by
      simpa only [Metric.mem_closedBall,Prod.dist_eq,dist_self,dist_zero_right,max_eq_left (norm_nonneg v)] using hv
    obtain ⟨hinit,hder⟩ := hα (v,0) hvr
    refine ⟨hinit,?_⟩
    intro t ht
    apply (hder t (by simpa only [zero_sub,zero_add] using Set.Ioo_subset_Icc_self ht)).hasDerivAt
    exact Icc_mem_nhds (by simpa only [zero_sub] using ht.1) (by simpa only [zero_add] using ht.2)
  have hfirst : ∀ v : E, ‖v‖ ≤ (r : ℝ) → ∀ t ∈ Set.Ioo (-ε) ε, (α ((v,0),t)).1 = v := by
    intro v hv t ht
    have hd : ∀ s ∈ Set.Ioo (-ε) ε, HasDerivAt (fun s => (α ((v,0),s)).1) (0 : E) s :=
      fun s hs => ((hα' v hv).2 s hs).fst
    have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-ε) ε).isPreconnected
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) ht hz
    rw [(hα' v hv).1] at he
    exact he
  let f : E × ℝ → E := fun p => (α ((p.1,0),p.2)).2
  have hdomain : Metric.closedBall (0 : E × E) (r : ℝ) ×ˢ Set.Icc (0-ε) (0+ε) ∈
      𝓝 (((0 : E),(0 : E)),(0 : ℝ)) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod
      (Metric.closedBall_mem_nhds (0 : E × E) (by exact_mod_cast hr))
      (Icc_mem_nhds (by linarith) (by linarith))
  have hαat : ContinuousAt α (((0 : E),(0 : E)),(0 : ℝ)) := hαcont.continuousAt hdomain
  have hmap : ContinuousAt (fun p : E × ℝ => ((p.1,(0 : E)),p.2)) (0,0) :=
    (continuousAt_fst.prodMk continuousAt_const).prodMk continuousAt_snd
  have hmapAll : Continuous (fun p : E × ℝ => ((p.1,(0 : E)),p.2)) :=
    (continuous_fst.prodMk continuous_const).prodMk continuous_snd
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hcontOn : ContinuousOn f (Metric.ball (0 : E) r ×ˢ Set.Ioo (-ε) ε) := by
    intro p hp
    have hv : ‖p.1‖ < (r : ℝ) := by simpa only [Metric.mem_ball,dist_zero_right] using hp.1
    have hvr : (p.1,(0 : E)) ∈ Metric.ball (0,0) (r : ℝ) := by
      simpa only [Metric.mem_ball,Prod.dist_eq,dist_self,dist_zero_right,max_eq_left (norm_nonneg p.1)] using hv
    have hdom : Metric.closedBall (0 : E × E) (r : ℝ) ×ˢ Set.Icc (0-ε) (0+ε) ∈
        𝓝 ((p.1,(0 : E)),p.2) := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (Metric.closedBall_mem_nhds_of_mem hvr)
        (Icc_mem_nhds (by simpa only [zero_sub] using hp.2.1) (by simpa only [zero_add] using hp.2.2))
    exact ((hαcont.continuousAt hdom).comp
      (f := fun p : E × ℝ => ((p.1,(0 : E)),p.2)) hmapAll.continuousAt).snd.continuousWithinAt
  refine ⟨f,(hαat.comp (f := fun p : E × ℝ => ((p.1,(0 : E)),p.2)) hmap).snd,
    ⟨Metric.ball (0 : E) r ×ˢ Set.Ioo (-ε) ε,Metric.isOpen_ball.prod isOpen_Ioo,
      ⟨Metric.mem_ball_self hrR,hz⟩,hcontOn⟩,?_,?_⟩
  · filter_upwards [Metric.ball_mem_nhds (0 : E) (show (0 : ℝ) < r by exact_mod_cast hr)] with v hv
    have hv' : ‖v‖ ≤ (r : ℝ) := le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hv)
    change (α ((v,0),0)).2 = 0
    rw [(hα' v hv').1]
  · have hnear : ∀ᶠ p : E × ℝ in 𝓝 (0,0), ‖p.1‖ < (r : ℝ) ∧ |p.2| < ε := by
      have hfst : Filter.Tendsto (fun p : E × ℝ => p.1) (𝓝 (0,0)) (𝓝 0) := continuousAt_fst
      have hsnd : Filter.Tendsto (fun p : E × ℝ => p.2) (𝓝 (0,0)) (𝓝 0) := continuousAt_snd
      filter_upwards [hfst.eventually (Metric.ball_mem_nhds (0 : E) (show (0 : ℝ) < r by exact_mod_cast hr)),
        hsnd.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)] with p hp ht
      exact ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hp,
        by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht⟩
    filter_upwards [hnear] with p hp
    have hd := ((hα' p.1 hp.1.le).2 p.2 (abs_lt.mp hp.2)).snd
    change HasDerivAt (fun t => (α ((p.1,0),t)).2)
      (A ((α ((p.1,0),p.2)).2) ((α ((p.1,0),p.2)).1)) p.2 at hd
    rw [hfirst p.1 hp.1.le p.2 (abs_lt.mp hp.2)] at hd
    exact hd
end DirectedCycles
