import DirectedCycles.LocalGroupSmoothness
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E H]

/-- Smoothness at zero propagates to every interior parameter using actual
local translation and the prescribed parameter interval. -/
theorem smooth_local_curve_contMDiffAt_interior (Q : LocalGroupAlgebra H)
    (hQ : LocalGroupSmoothness (E := E) Q) (f : ℝ → H) (hf0 : f 0 = Q.one)
    (hf : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ f 0)
    (hadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t)))
    {t : ℝ} (ht : |t| < 1) : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ f t := by
  obtain ⟨m,hm,hmrel⟩ := hQ.smooth_mul (f t) Q.one ⟨f t,Q.mul_one _⟩
  have hg : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ (fun s : ℝ => f (s-t)) t :=
    hf.comp_of_eq (contMDiffAt_id.sub contMDiffAt_const) (sub_self t)
  have hp : ContMDiffAt 𝓘(ℝ,ℝ) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun s : ℝ => (f t,f (s-t))) t := contMDiffAt_const.prodMk hg
  have hs : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ (fun s : ℝ => m (f t,f (s-t))) t :=
    hm.comp_of_eq hp (by simp only [sub_self,hf0])
  have hpT : Filter.Tendsto (fun s : ℝ => (f t,f (s-t))) (𝓝 t) (𝓝 (f t,Q.one)) := by
    simpa only [sub_self,hf0] using hp.continuousAt.tendsto
  have hnear' : ∀ᶠ s : ℝ in 𝓝 t, Q.mulRel (f t) (f (s-t)) (m (f t,f (s-t))) := by
    exact hpT.eventually hmrel
  apply hs.congr_of_eventuallyEq
  filter_upwards [hnear',Metric.ball_mem_nhds t (sub_pos.2 ht)] with s hs hst
  have hb : |s-t| < 1-|t| := by simpa only [Metric.mem_ball,Real.dist_eq] using hst
  have hh := hadd t (s-t) (by linarith)
  rw [add_sub_cancel] at hh
  exact Q.unique hh hs

/-- The actual curve is continuous on its closed parameter segment, including
both endpoints. Endpoint continuity uses two half-parameter factors. -/
theorem smooth_local_curve_continuousOn_segment (Q : LocalGroupAlgebra H)
    (hQ : LocalGroupSmoothness (E := E) Q) (f : ℝ → H) (hf0 : f 0 = Q.one)
    (hf : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ f 0)
    (hadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t))) :
    ContinuousOn f (Set.Icc (-1 : ℝ) 1) := by
  intro t ht
  have ht1 : |t| ≤ 1 := abs_le.2 ht
  have habs : |t/2| = |t|/2 := by rw [abs_div]; norm_num
  have htHalf : |t/2| < 1 := by rw [habs]; linarith
  have hfHalf := smooth_local_curve_contMDiffAt_interior Q hQ f hf0 hf hadd htHalf
  have hrel := hadd (t/2) (t/2) (by rw [habs]; linarith)
  obtain ⟨m,hm,hmrel⟩ := hQ.smooth_mul (f (t/2)) (f (t/2)) ⟨f (t/2+t/2),hrel⟩
  have hg : ContinuousAt (fun s : ℝ => f (s/2)) t := hfHalf.continuousAt.comp (f := fun s : ℝ => s/2) ((continuous_id : Continuous (fun s : ℝ => s)).div_const (2 : ℝ)).continuousAt
  have hp : ContinuousAt (fun s : ℝ => (f (s/2),f (s/2))) t := hg.prodMk hg
  have hs : ContinuousAt (fun s : ℝ => m (f (s/2),f (s/2))) t := hm.continuousAt.comp (f := fun s : ℝ => (f (s/2),f (s/2))) hp
  have hnear : ∀ᶠ s : ℝ in 𝓝 t, Q.mulRel (f (s/2)) (f (s/2)) (m (f (s/2),f (s/2))) :=
    hp.tendsto.eventually hmrel
  have heq : f =ᶠ[𝓝[Set.Icc (-1 : ℝ) 1] t] (fun s => m (f (s/2),f (s/2))) := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear,self_mem_nhdsWithin] with s hs hst
    have hb : |s/2|+|s/2| ≤ 1 := by
      rw [abs_div]
      norm_num
      linarith [abs_le.2 hst]
    have hh := hadd (s/2) (s/2) hb
    have he : s/2+s/2 = s := by ring
    rw [he] at hh
    exact Q.unique hh hs
  apply hs.continuousWithinAt.congr_of_eventuallyEq heq
  have he : t/2+t/2 = t := by ring
  rw [he] at hrel
  exact Q.unique hrel hmrel.self_of_nhds
end DirectedCycles
