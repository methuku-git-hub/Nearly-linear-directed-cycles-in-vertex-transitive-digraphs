import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniqueness of actual ODE solutions turns a left-invariant coordinate
field into a genuine local one-parameter multiplication law. -/
theorem local_integral_curve_multiplication (μ : E × E → E) (V : E → E)
    (hμ : ContDiffAt ℝ 1 μ (0,0)) (hV : ContDiffAt ℝ 1 V 0)
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hinv : ∀ᶠ p : E × E in 𝓝 (0,0),
      (fderiv ℝ μ p) (0,V p.2) = V (μ p))
    (f : ℝ → E) (hf0 : f 0 = 0)
    (hder : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), HasDerivAt f (V (f t)) t) :
    ∃ r : ℝ, 0 < r ∧ ∀ s t : ℝ, |s|+|t| ≤ r → f (s+t) = μ (f s,f t) := by
  obtain ⟨K,S,hS,hLip⟩ := hV.exists_lipschitzOnWith
  have hc : ContinuousAt f 0 := (hder.self_of_nhds).continuousAt
  have h0 : μ (0,0) = 0 := hl.self_of_nhds
  have hdiff : ∀ᶠ p : E × E in 𝓝 (0,0), DifferentiableAt ℝ μ p :=
    (hμ.eventually (by simp)).mono (fun p hp => hp.differentiableAt one_ne_zero)
  have hf : Filter.Tendsto f (𝓝 0) (𝓝 0) := by simpa only [hf0] using hc.tendsto
  have hfst : Filter.Tendsto (fun p : ℝ × ℝ => p.1) (𝓝 (0,0)) (𝓝 0) := continuousAt_fst
  have hsnd : Filter.Tendsto (fun p : ℝ × ℝ => p.2) (𝓝 (0,0)) (𝓝 0) := continuousAt_snd
  have hsum : Filter.Tendsto (fun p : ℝ × ℝ => p.1+p.2) (𝓝 (0,0)) (𝓝 0) := by
    simpa only [zero_add] using hfst.add hsnd
  have hp : Filter.Tendsto (fun p : ℝ × ℝ => (f p.1,f p.2)) (𝓝 (0,0)) (𝓝 (0,0)) :=
    (hf.comp hfst).prodMk_nhds (hf.comp hsnd)
  have hmu : Filter.Tendsto μ (𝓝 (0,0)) (𝓝 0) := by simpa only [h0] using hμ.continuousAt.tendsto
  have hgood : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0),
      HasDerivAt f (V (f p.2)) p.2 ∧ HasDerivAt f (V (f (p.1+p.2))) (p.1+p.2) ∧
      DifferentiableAt ℝ μ (f p.1,f p.2) ∧
      (fderiv ℝ μ (f p.1,f p.2)) (0,V (f p.2)) = V (μ (f p.1,f p.2)) ∧
      μ (f p.1,0) = f p.1 ∧ f (p.1+p.2) ∈ S ∧ μ (f p.1,f p.2) ∈ S := by
    filter_upwards [hsnd.eventually hder,hsum.eventually hder,hp.eventually hdiff,
      hp.eventually hinv,(hf.comp hfst).eventually hl,(hf.comp hsum).eventually hS,
      (hmu.comp hp).eventually hS] with p hd hs hm hi hl hfS hmS
    exact ⟨hd,hs,hm,hi,hl,hfS,hmS⟩
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hg : ∀ s t : ℝ, |s| < ρ → |t| < ρ →
      HasDerivAt f (V (f t)) t ∧ HasDerivAt f (V (f (s+t))) (s+t) ∧
      DifferentiableAt ℝ μ (f s,f t) ∧
      (fderiv ℝ μ (f s,f t)) (0,V (f t)) = V (μ (f s,f t)) ∧
      μ (f s,0) = f s ∧ f (s+t) ∈ S ∧ μ (f s,f t) ∈ S := by
    intro s t hs ht
    exact hball (show (s,t) ∈ Metric.ball (0,0) ρ from by
      simpa only [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,sub_zero] using max_lt hs ht)
  refine ⟨ρ/2,by positivity,?_⟩
  intro s t hst
  have hs : |s| < ρ := by linarith [abs_nonneg t]
  have ht : |t| < ρ := by linarith [abs_nonneg s]
  have ha : ∀ z ∈ Set.Ioo (-ρ) ρ,
      HasDerivAt (fun z => f (s+z)) (V (f (s+z))) z ∧ f (s+z) ∈ S := by
    intro z hz
    have hh := hg s z hs (abs_lt.mpr hz)
    refine ⟨?_,hh.2.2.2.2.2.1⟩
    have hd := hh.2.1.scomp z ((hasDerivAt_id z).const_add s)
    simpa only [Function.comp_def,one_smul] using hd
  have hb : ∀ z ∈ Set.Ioo (-ρ) ρ,
      HasDerivAt (fun z => μ (f s,f z)) (V (μ (f s,f z))) z ∧ μ (f s,f z) ∈ S := by
    intro z hz
    have hh := hg s z hs (abs_lt.mpr hz)
    refine ⟨?_,hh.2.2.2.2.2.2⟩
    have hd := hh.2.2.1.hasFDerivAt.comp_hasDerivAt z ((hasDerivAt_const z (f s)).prodMk hh.1)
    simpa only [Function.comp_def,hh.2.2.2.1] using hd
  have he0 : f (s+0) = μ (f s,f 0) := by
    rw [add_zero,hf0,(hg s 0 hs (by simpa only [abs_zero] using hρ)).2.2.2.2.1]
  exact ODE_solution_unique_of_mem_Ioo (v := fun _ => V) (s := fun _ => S)
    (fun _ _ => hLip) (show (0 : ℝ) ∈ Set.Ioo (-ρ) ρ by constructor <;> linarith)
    ha hb he0 (abs_lt.mp ht)
end DirectedCycles
