module

public import DirectedCycles.SmoothLocalIdentityCoordinates
public import DirectedCycles.LocalExponentialCoordinateExistence
public import DirectedCycles.LocalCoordinateChangeMultiplication

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [ChartedSpace E G] [IsManifold 𝓘(ℝ,E) ∞ G]

/-- Actual exponential coordinates on a smooth local group. The smooth base
chart and strict coordinate derivative are retained for uniform conjugation
bounds. This is a data type; existence is proved below from local smoothness. -/
structure LocalExponentialData (L : LocalGroupAlgebra G) where
  chart : OpenPartialHomeomorph E G
  zero_mem : (0 : E) ∈ chart.source
  zero : chart 0 = L.one
  product : E × E → E
  product_zero : product (0,0) = 0
  product_derivative : HasFDerivAt product
    (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (0,0)
  product_rel : ∀ᶠ p : E × E in 𝓝 (0,0), L.mulRel (chart p.1) (chart p.2) (chart (product p))
  radius : ℝ
  radius_pos : 0 < radius
  ball_source : Metric.ball (0 : E) radius ⊆ chart.source
  radial : ∀ v : E, ‖v‖ < radius → ∀ s t : ℝ, |s|+|t| ≤ 1 →
    L.mulRel (chart (s • v)) (chart (t • v)) (chart ((s+t) • v))
  baseChart : OpenPartialHomeomorph E G
  base_zero_mem : (0 : E) ∈ baseChart.source
  base_zero : baseChart 0 = L.one
  base_smooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ baseChart 0
  base_inverse_smooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ baseChart.symm L.one
  coordinateMap : E → E
  coordinate_zero : coordinateMap 0 = 0
  coordinate_derivative : HasStrictFDerivAt coordinateMap (ContinuousLinearMap.id ℝ E) 0
  chart_eq : ∀ v : E, chart v = baseChart (coordinateMap v)

/-- Every smooth local group has actual local exponential data. Every field,
including the radial law and the strict coordinate derivative, is constructed
from the smooth local multiplication and uniform ODE existence. -/
theorem smooth_local_exponential_data (L : LocalGroupAlgebra G)
    (hL : LocalGroupSmoothness (E := E) L) : Nonempty (LocalExponentialData (E := E) L) := by
  obtain ⟨a,ha0,ha1,haSmooth,hbSmooth,μ,hμ0,hμ,hrel,hl,hr,hassoc⟩ := smooth_local_identity_coordinates L hL
  obtain ⟨F,hF0,hF,R,hR,hradial⟩ := exists_local_exponential_coordinate_map μ hμ hl hr hassoc
  have hFe : HasStrictFDerivAt F (ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap 0 := hF
  let b := hFe.toOpenPartialHomeomorph F
  let c := b.trans a
  have hb0 : (0 : E) ∈ b.source := hFe.mem_toOpenPartialHomeomorph_source
  have hc0 : (0 : E) ∈ c.source := ⟨hb0,by change F 0 ∈ a.source; simpa only [hF0] using ha0⟩
  have hc1 : c 0 = L.one := by change a (F 0) = L.one; rw [hF0,ha1]
  have hFT : Filter.Tendsto F (𝓝 (0 : E)) (𝓝 (0 : E)) := by
    simpa only [hF0] using hF.continuousAt.tendsto
  have hfst : Filter.Tendsto (fun p : E × E => p.1) (𝓝 (0,0)) (𝓝 0) := continuousAt_fst
  have hsnd : Filter.Tendsto (fun p : E × E => p.2) (𝓝 (0,0)) (𝓝 0) := continuousAt_snd
  have hpair : Filter.Tendsto (fun p : E × E => (F p.1,F p.2)) (𝓝 (0,0)) (𝓝 (0,0)) :=
    (hFT.comp hfst).prodMk_nhds (hFT.comp hsnd)
  have hnear : ∀ᶠ p : E × E in 𝓝 (0,0),
      L.mulRel (c p.1) (c p.2) (a (μ (F p.1,F p.2))) := hpair.eventually hrel
  obtain ⟨ν,hν0,hν,hνeq⟩ := local_coordinate_change_multiplication F hF0 hF μ
    (hμ.differentiableAt (by simp)) hl hr
  have hνrel : ∀ᶠ p : E × E in 𝓝 (0,0), L.mulRel (c p.1) (c p.2) (c (ν p)) := by
    filter_upwards [hnear,hνeq] with p hp he
    change L.mulRel (c p.1) (c p.2) (a (F (ν p)))
    rw [he]
    exact hp
  obtain ⟨δ,hδ,hδrel⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨η,hη,hηsource⟩ := Metric.mem_nhds_iff.mp (c.open_source.mem_nhds hc0)
  let r := min R (min δ η)
  have hr0 : 0 < r := lt_min hR (lt_min hδ hη)
  have hrR : r ≤ R := min_le_left _ _
  have hrδ : r ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hrη : r ≤ η := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨{
    chart := c
    zero_mem := hc0
    zero := hc1
    product := ν
    product_zero := hν0
    product_derivative := hν
    product_rel := hνrel
    radius := r
    radius_pos := hr0
    ball_source := (Metric.ball_subset_ball hrη).trans hηsource
    radial := ?_
    baseChart := a
    base_zero_mem := ha0
    base_zero := ha1
    base_smooth := haSmooth
    base_inverse_smooth := hbSmooth
    coordinateMap := F
    coordinate_zero := hF0
    coordinate_derivative := hF
    chart_eq := fun _ => rfl }⟩
  intro v hv s t hst
  have hs : |s| ≤ 1 := by linarith [abs_nonneg t]
  have ht : |t| ≤ 1 := by linarith [abs_nonneg s]
  have hnorm : ∀ a : ℝ, |a| ≤ 1 → ‖a • v‖ < δ := by
    intro a ha
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg v)).trans_lt
      (by simpa only [one_mul] using hv.trans_le hrδ)
  have hp : (s • v,t • v) ∈ Metric.ball ((0 : E),(0 : E)) δ := by
    simpa only [Metric.mem_ball,Prod.dist_eq,dist_zero_right] using max_lt (hnorm s hs) (hnorm t ht)
  have hh := hδrel hp
  change L.mulRel (c (s • v)) (c (t • v)) (a (F ((s+t) • v)))
  rw [hradial v (hv.trans_le hrR) s t hst]
  exact hh
end DirectedCycles
