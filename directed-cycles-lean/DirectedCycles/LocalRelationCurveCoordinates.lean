module

public import DirectedCycles.SmoothLocalIdentityCoordinates

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E]

/-- A continuous local relation curve obeys the genuine coordinate product
law on a smaller interval. Every inverse chart and product domain is checked. -/
theorem local_relation_curve_coordinate_law (Q : LocalGroupAlgebra H)
    (a : OpenPartialHomeomorph E H) (ha0 : (0 : E) ∈ a.source) (ha1 : a 0 = Q.one)
    (μ : E × E → E) (hμ0 : μ (0,0) = 0) (hμ : ContinuousAt μ (0,0))
    (hrel : ∀ᶠ p : E × E in 𝓝 (0,0), Q.mulRel (a p.1) (a p.2) (a (μ p)))
    (f : ℝ → H) (hf0 : f 0 = Q.one) (hfc : ContinuousAt f 0) {r : ℝ} (hr : 0 < r)
    (hflaw : ∀ s t : ℝ, |s|+|t| ≤ r → Q.mulRel (f s) (f t) (f (s+t))) :
    let g := fun t => a.symm (f t)
    g 0 = 0 ∧ ContinuousAt g 0 ∧ ∃ s : ℝ, 0 < s ∧
      ∀ u v : ℝ, |u|+|v| ≤ s → g (u+v) = μ (g u,g v) := by
  let g : ℝ → E := fun t => a.symm (f t)
  have ht : Q.one ∈ a.target := ha1 ▸ a.mapsTo ha0
  have hg0 : g 0 = 0 := by change a.symm (f 0) = 0; rw [hf0,← ha1]; exact a.left_inv ha0
  have hgc : ContinuousAt g 0 := (a.symm.continuousAt (hf0.symm ▸ ht)).comp hfc
  have hfT : Filter.Tendsto f (𝓝 0) (𝓝 Q.one) := by simpa only [hf0] using hfc.tendsto
  have hgT : Filter.Tendsto g (𝓝 0) (𝓝 (0 : E)) := by simpa only [hg0] using hgc.tendsto
  have hfst : Filter.Tendsto (fun p : ℝ × ℝ => p.1) (𝓝 (0,0)) (𝓝 0) := continuousAt_fst
  have hsnd : Filter.Tendsto (fun p : ℝ × ℝ => p.2) (𝓝 (0,0)) (𝓝 0) := continuousAt_snd
  have hpT := (hgT.comp hfst).prodMk_nhds (hgT.comp hsnd)
  have hmT : Filter.Tendsto (fun p : ℝ × ℝ => μ (g p.1,g p.2)) (𝓝 (0,0)) (𝓝 (0 : E)) := by
    have h := (show Filter.Tendsto μ (𝓝 (0,0)) (𝓝 (0 : E)) from by simpa only [hμ0] using hμ.tendsto).comp hpT
    simpa only [Function.comp_def] using h
  have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0),
      Q.mulRel (f p.1) (f p.2) (a (μ (g p.1,g p.2))) ∧ μ (g p.1,g p.2) ∈ a.source := by
    filter_upwards [hpT.eventually hrel,(hfT.comp hfst).eventually (a.open_target.mem_nhds ht),
      (hfT.comp hsnd).eventually (a.open_target.mem_nhds ht),
      hmT.eventually (a.open_source.mem_nhds ha0)] with p hp hf1 hf2 hm
    have h1 : a (g p.1) = f p.1 := a.right_inv hf1
    have h2 : a (g p.2) = f p.2 := a.right_inv hf2
    exact ⟨by simpa only [Function.comp_def,h1,h2] using hp,hm⟩
  obtain ⟨δ,hδ,hδnear⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨hg0,hgc,min r (δ/2),lt_min hr (by positivity),?_⟩
  intro u v huv
  have hu : |u| < δ := by have := min_le_right r (δ/2); linarith [abs_nonneg v]
  have hv : |v| < δ := by have := min_le_right r (δ/2); linarith [abs_nonneg u]
  obtain ⟨hm,hs⟩ := hδnear (show (u,v) ∈ Metric.ball (0,0) δ from by
    simpa only [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,sub_zero] using max_lt hu hv)
  have he := Q.unique (hflaw u v (huv.trans (min_le_left _ _))) hm
  change a.symm (f (u+v)) = μ (g u,g v)
  rw [he,a.left_inv hs]
end DirectedCycles
