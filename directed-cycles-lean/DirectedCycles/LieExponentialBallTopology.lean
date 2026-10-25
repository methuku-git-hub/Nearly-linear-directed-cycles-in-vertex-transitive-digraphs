module

public import DirectedCycles.LieExponentialLocalCoordinates
public import DirectedCycles.LieExponentialSymmetry
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ,E) ∞ G]

theorem lie_exponential_ball_inv_mem {ρ : ℝ} {x : G}
    (hx : x ∈ (lieExponential (G := G) (E := E)) '' Metric.ball (0 : E) ρ) :
    x⁻¹ ∈ (lieExponential (G := G) (E := E)) '' Metric.ball (0 : E) ρ := by
  obtain ⟨v,hv,rfl⟩ := hx
  refine ⟨-v,?_,lieExponential_neg v⟩
  simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hv

/-- In a common actual coordinate window the exponential images of all
open balls are open; this is obtained from the constructed inverse chart. -/
theorem lie_exponential_small_ball_open :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, r ≤ R →
      IsOpen ((lieExponential (G := G) (E := E)) '' Metric.ball (0 : E) r) := by
  obtain ⟨e,he0,_,he⟩ := lie_exponential_local_coordinates (G := G) (E := E)
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds he0)
  refine ⟨R,hR,?_⟩
  intro r hr
  have hsub : Metric.ball (0 : E) r ⊆ e.source := (Metric.ball_subset_ball hr).trans hball
  have heq : (lieExponential (G := G) (E := E)) '' Metric.ball (0 : E) r = e '' Metric.ball (0 : E) r := by
    apply Set.image_congr
    intro v hv
    exact (he v (hsub hv)).symm
  rw [heq]
  exact e.isOpen_image_of_subset_source Metric.isOpen_ball hsub

/-- Compact inner balls and open outer balls can be placed inside any
prescribed target identity neighbourhood, uniformly for all smaller radii. -/
theorem lie_exponential_ball_sandwich [FiniteDimensional ℝ E]
    (W : Set G) (hW : W ∈ 𝓝 (1 : G)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      IsCompact ((lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) r) ∧
      IsOpen ((lieExponential (G := G) (E := E)) '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r)) ∧
      (lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) r ⊆
        (lieExponential (G := G) (E := E)) '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r) ∧
      (lieExponential (G := G) (E := E)) '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r) ⊆ W := by
  obtain ⟨Ro,hRo,ho⟩ := lie_exponential_small_ball_open (G := G) (E := E)
  have hcont := (lie_exponential_continuous (G := G) (E := E)).continuousAt (x := (0 : E))
  have hpre : (lieExponential (G := G) (E := E)) ⁻¹' W ∈ 𝓝 (0 : E) := by
    apply hcont.preimage_mem_nhds
    simpa only [lieExponential_zero] using hW
  obtain ⟨Rw,hRw,hw⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨min Ro Rw/2,div_pos (lt_min hRo hRw) (by norm_num),?_⟩
  intro r hr hrr
  have hscale : 2*r < min Ro Rw := by linarith [(lt_div_iff₀ (show (0 : ℝ) < 2 by norm_num)).1 hrr]
  have hro : (1001/1000 : ℝ)*r < Ro := by have := hscale.trans_le (min_le_left _ _); linarith
  have hrw : (1001/1000 : ℝ)*r < Rw := by have := hscale.trans_le (min_le_right _ _); linarith
  refine ⟨(isCompact_closedBall (0 : E) r).image (lie_exponential_continuous (G := G) (E := E)),
    ho _ hro.le,Set.image_mono (Metric.closedBall_subset_ball (by linarith)),?_⟩
  rintro x ⟨v,hv,rfl⟩
  exact hw ((Metric.ball_subset_ball hrw.le) hv)
end DirectedCycles
