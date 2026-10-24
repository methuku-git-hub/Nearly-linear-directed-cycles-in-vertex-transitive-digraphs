import DirectedCycles.SmoothParameterIntegralCurves

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The augmented ODE construction supplies an actual uniform Lipschitz bound
in the tangent parameter, as well as joint continuity and the differential
equations on a common interval. -/
theorem exists_lipschitz_parameter_integral_curves (A : E → E →L[ℝ] E)
    (hA : ContDiffAt ℝ 1 A 0) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧ ∃ K : NNReal, ∃ f : E × ℝ → E,
      (∀ v : E, ‖v‖ ≤ r → f (v,0) = 0 ∧ ∀ t : ℝ, |t| < ε →
        HasDerivAt (fun t => f (v,t)) (A (f (v,t)) v) t) ∧
      (∀ t : ℝ, |t| < ε → LipschitzOnWith K (fun v => f (v,t)) (Metric.closedBall 0 r)) ∧
      ContinuousOn f (Metric.closedBall 0 r ×ˢ Set.Icc (-ε) ε) := by
  let V : E × E → E × E := fun p => (0,A p.2 p.1)
  have hV : ContDiffAt ℝ 1 V (0,0) := contDiffAt_const.prodMk
    ((hA.comp (0,0) contDiffAt_snd).clm_apply contDiffAt_fst)
  obtain ⟨ε,hε,a,r,B,K,hr,hpl⟩ := IsPicardLindelof.of_contDiffAt_one hV
  obtain ⟨α,hα,L,hLip⟩ := (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  have hz : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by constructor <;> linarith
  have hvr : ∀ v : E, ‖v‖ ≤ (r : ℝ) → (v,(0 : E)) ∈ Metric.closedBall (0,0) (r : ℝ) := by
    intro v hv
    simpa only [Metric.mem_closedBall,Prod.dist_eq,dist_self,dist_zero_right,max_eq_left (norm_nonneg v)] using hv
  have hα' : ∀ v : E, ‖v‖ ≤ (r : ℝ) → α (v,0) 0 = (v,0) ∧
      ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt (α (v,0)) (V (α (v,0) t)) t := by
    intro v hv
    obtain ⟨hinit,hder⟩ := hα (v,0) (hvr v hv)
    refine ⟨hinit,?_⟩
    intro t ht
    apply (hder t (by simpa only [zero_sub,zero_add] using Set.Ioo_subset_Icc_self ht)).hasDerivAt
    exact Icc_mem_nhds (by simpa only [zero_sub] using ht.1) (by simpa only [zero_add] using ht.2)
  have hfirst : ∀ v : E, ‖v‖ ≤ (r : ℝ) → ∀ t ∈ Set.Ioo (-ε) ε, (α (v,0) t).1 = v := by
    intro v hv t ht
    have hd : ∀ s ∈ Set.Ioo (-ε) ε, HasDerivAt (fun s => (α (v,0) s).1) (0 : E) s :=
      fun s hs => ((hα' v hv).2 s hs).fst
    have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-ε) ε).isPreconnected
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) ht hz
    rw [(hα' v hv).1] at he
    exact he
  let f : E × ℝ → E := fun p => (α (p.1,0) p.2).2
  refine ⟨r,ε,by exact_mod_cast hr,hε,L,f,?_,?_,?_⟩
  · intro v hv
    refine ⟨?_,?_⟩
    · change (α (v,0) 0).2 = 0
      rw [(hα' v hv).1]
    · intro t ht
      have hd := ((hα' v hv).2 t (abs_lt.mp ht)).snd
      change HasDerivAt (fun t => (α (v,0) t).2) (A ((α (v,0) t).2) ((α (v,0) t).1)) t at hd
      rw [hfirst v hv t (abs_lt.mp ht)] at hd
      exact hd
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro v hv w hw
    have hv' : ‖v‖ ≤ (r : ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
    have hw' : ‖w‖ ≤ (r : ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
    have hh := (hLip t (by simpa only [zero_sub,zero_add] using Set.Ioo_subset_Icc_self (abs_lt.mp ht))).dist_le_mul
      (v,0) (hvr v hv') (w,0) (hvr w hw')
    calc
      dist (f (v,t)) (f (w,t)) ≤ dist (α (v,0) t) (α (w,0) t) := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      _ ≤ (L : ℝ)*dist v w := by simpa only [Prod.dist_eq,dist_self,max_eq_left dist_nonneg] using hh
  · have hαcont : ContinuousOn (Function.uncurry α)
        (Metric.closedBall (0 : E × E) (r : ℝ) ×ˢ Set.Icc (0-ε) (0+ε)) := by
      apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L _ hLip
      exact fun x hx => HasDerivWithinAt.continuousOn (hα x hx).2
    have hmap : Continuous (fun p : E × ℝ => ((p.1,(0 : E)),p.2)) :=
      (continuous_fst.prodMk continuous_const).prodMk continuous_snd
    apply (hαcont.comp hmap.continuousOn ?_).snd
    intro p hp
    exact ⟨hvr p.1 (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1),
      by simpa only [zero_sub,zero_add] using hp.2⟩
end DirectedCycles
