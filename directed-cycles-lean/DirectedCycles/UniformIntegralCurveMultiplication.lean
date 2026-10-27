module

public import DirectedCycles.LocalIntegralCurveMultiplication

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup P]

/-- Joint continuity and a common local Lipschitz bound give a common
parameter interval for the multiplication laws of an entire family of ODE
curves. No parameter differentiability is assumed. -/
theorem uniform_integral_curve_multiplication (μ : E × E → E) (V : P → E → E)
    (hμ : ContDiffAt ℝ 1 μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hinv : ∀ᶠ p : E × E in 𝓝 (0,0), ∀ v : P,
      (fderiv ℝ μ p) (0,V v p.2) = V v (μ p))
    (S : Set E) (hS : S ∈ 𝓝 (0 : E)) (K : NNReal)
    (hLip : ∀ᶠ v : P in 𝓝 0, LipschitzOnWith K (V v) S)
    (f : P × ℝ → E) (hc : ContinuousAt f (0,0))
    (hf0 : ∀ᶠ v : P in 𝓝 0, f (v,0) = 0)
    (hder : ∀ᶠ p : P × ℝ in 𝓝 (0,0), HasDerivAt (fun t => f (p.1,t)) (V p.1 (f p)) p.2) :
    ∃ R r : ℝ, 0 < R ∧ 0 < r ∧ ∀ v : P, ‖v‖ < R →
      ∀ s t : ℝ, |s|+|t| ≤ r → f (v,s+t) = μ (f (v,s),f (v,t)) := by
  have hf00 : f (0,0) = 0 := hf0.self_of_nhds
  have hf : Filter.Tendsto f (𝓝 (0,0)) (𝓝 0) := by simpa only [hf00] using hc.tendsto
  have h0 : μ (0,0) = 0 := hl.self_of_nhds
  have hmu : Filter.Tendsto μ (𝓝 (0,0)) (𝓝 0) := by simpa only [h0] using hμ.continuousAt.tendsto
  have hdiff : ∀ᶠ p : E × E in 𝓝 (0,0), DifferentiableAt ℝ μ p :=
    (hμ.eventually (by simp)).mono (fun p hp => hp.differentiableAt one_ne_zero)
  have hv : Filter.Tendsto (fun p : P × (ℝ × ℝ) => p.1) (𝓝 (0,(0,0))) (𝓝 0) := continuousAt_fst
  have hs : Filter.Tendsto (fun p : P × (ℝ × ℝ) => p.2.1) (𝓝 (0,(0,0))) (𝓝 0) := continuousAt_snd.fst
  have ht : Filter.Tendsto (fun p : P × (ℝ × ℝ) => p.2.2) (𝓝 (0,(0,0))) (𝓝 0) := continuousAt_snd.snd
  have hsum : Filter.Tendsto (fun p : P × (ℝ × ℝ) => p.2.1+p.2.2) (𝓝 (0,(0,0))) (𝓝 0) := by
    simpa only [zero_add] using hs.add ht
  have hfs := hf.comp (hv.prodMk_nhds hs)
  have hft := hf.comp (hv.prodMk_nhds ht)
  have hfsum := hf.comp (hv.prodMk_nhds hsum)
  have hpair := hfs.prodMk_nhds hft
  have hgood : ∀ᶠ p : P × (ℝ × ℝ) in 𝓝 (0,(0,0)),
      LipschitzOnWith K (V p.1) S ∧ f (p.1,0) = 0 ∧
      HasDerivAt (fun t => f (p.1,t)) (V p.1 (f (p.1,p.2.2))) p.2.2 ∧
      HasDerivAt (fun t => f (p.1,t)) (V p.1 (f (p.1,p.2.1+p.2.2))) (p.2.1+p.2.2) ∧
      DifferentiableAt ℝ μ (f (p.1,p.2.1),f (p.1,p.2.2)) ∧
      (fderiv ℝ μ (f (p.1,p.2.1),f (p.1,p.2.2))) (0,V p.1 (f (p.1,p.2.2))) =
        V p.1 (μ (f (p.1,p.2.1),f (p.1,p.2.2))) ∧
      μ (f (p.1,p.2.1),0) = f (p.1,p.2.1) ∧
      f (p.1,p.2.1+p.2.2) ∈ S ∧ μ (f (p.1,p.2.1),f (p.1,p.2.2)) ∈ S := by
    filter_upwards [hv.eventually hLip,hv.eventually hf0,(hv.prodMk_nhds ht).eventually hder,
      (hv.prodMk_nhds hsum).eventually hder,hpair.eventually hdiff,hpair.eventually hinv,
      hfs.eventually hl,hfsum.eventually hS,(hmu.comp hpair).eventually hS] with p hL h0 hd hds hD hi hleft h1 h2
    exact ⟨hL,h0,hd,hds,hD,hi p.1,hleft,h1,h2⟩
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hg : ∀ v : P, ∀ s t : ℝ, ‖v‖ < ρ → |s| < ρ → |t| < ρ →
      LipschitzOnWith K (V v) S ∧ f (v,0) = 0 ∧
      HasDerivAt (fun t => f (v,t)) (V v (f (v,t))) t ∧
      HasDerivAt (fun t => f (v,t)) (V v (f (v,s+t))) (s+t) ∧
      DifferentiableAt ℝ μ (f (v,s),f (v,t)) ∧
      (fderiv ℝ μ (f (v,s),f (v,t))) (0,V v (f (v,t))) = V v (μ (f (v,s),f (v,t))) ∧
      μ (f (v,s),0) = f (v,s) ∧ f (v,s+t) ∈ S ∧ μ (f (v,s),f (v,t)) ∈ S := by
    intro v s t hv hs ht
    exact hball (show (v,(s,t)) ∈ Metric.ball (0,(0,0)) ρ from by
      simpa only [Metric.mem_ball,Prod.dist_eq,dist_zero_right,Real.norm_eq_abs] using max_lt hv (max_lt hs ht))
  refine ⟨ρ,ρ/2,hρ,by positivity,?_⟩
  intro v hv s t hst
  have hs : |s| < ρ := by linarith [abs_nonneg t]
  have ht : |t| < ρ := by linarith [abs_nonneg s]
  have hbase := hg v s 0 hv hs (by simpa only [abs_zero] using hρ)
  have ha : ∀ z ∈ Set.Ioo (-ρ) ρ,
      HasDerivAt (fun z => f (v,s+z)) (V v (f (v,s+z))) z ∧ f (v,s+z) ∈ S := by
    intro z hz
    have hh := (hg v s z hv hs (abs_lt.mpr hz)).2.2
    refine ⟨?_,hh.2.2.2.2.2.1⟩
    have hd := hh.2.1.scomp z ((hasDerivAt_id z).const_add s)
    simpa only [Function.comp_def,one_smul] using hd
  have hb : ∀ z ∈ Set.Ioo (-ρ) ρ,
      HasDerivAt (fun z => μ (f (v,s),f (v,z))) (V v (μ (f (v,s),f (v,z)))) z ∧
        μ (f (v,s),f (v,z)) ∈ S := by
    intro z hz
    have hh := (hg v s z hv hs (abs_lt.mpr hz)).2.2
    refine ⟨?_,hh.2.2.2.2.2.2⟩
    have hd := hh.2.2.1.hasFDerivAt.comp_hasDerivAt z ((hasDerivAt_const z (f (v,s))).prodMk hh.1)
    simpa only [Function.comp_def,hh.2.2.2.1] using hd
  have he0 : f (v,s+0) = μ (f (v,s),f (v,0)) := by
    rw [add_zero,hbase.2.1,hbase.2.2.2.2.2.2.1]
  exact ODE_solution_unique_of_mem_Ioo (v := fun _ => V v) (s := fun _ => S)
    (fun _ _ => hbase.1) (show (0 : ℝ) ∈ Set.Ioo (-ρ) ρ by constructor <;> linarith)
    ha hb he0 (abs_lt.mp ht)
end DirectedCycles
