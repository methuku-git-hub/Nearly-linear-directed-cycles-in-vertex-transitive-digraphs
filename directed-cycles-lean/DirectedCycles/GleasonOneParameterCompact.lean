import DirectedCycles.GleasonOneParameterWindow

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- A strict bound on the compact parameter interval gives a neighbourhood
in the compact-open topology. -/
theorem oneParameterWindow_mem_nhds (φ : OneParameter G) {T R : ℝ}
    (hφ : ∀ t : ℝ, |t| ≤ T → D.gauge (φ.eval t) < R) :
    D.oneParameterWindow T R ∈ 𝓝 φ := by
  let K : Set (Multiplicative ℝ) := Multiplicative.ofAdd '' Set.Icc (-T) T
  let U : Set G := {g | D.gauge g < R}
  have hK : IsCompact K := isCompact_Icc.image (show Continuous (Multiplicative.ofAdd : ℝ → Multiplicative ℝ) from continuous_id)
  have hU : IsOpen U := isOpen_lt D.continuous_gauge continuous_const
  have ho : IsOpen {ψ : OneParameter G | Set.MapsTo ψ K U} :=
    (ContinuousMap.isOpen_setOfPred_mapsTo hK hU).preimage
      (ContinuousMonoidHom.isInducing_toContinuousMap (Multiplicative ℝ) G).continuous
  have hmem : Set.MapsTo φ K U := by
    rintro _ ⟨t,ht,rfl⟩
    exact hφ t (abs_le.mpr ht)
  apply Filter.mem_of_superset (ho.mem_nhds hmem)
  intro ψ hψ t ht
  exact (hψ ⟨t,abs_le.mp ht,rfl⟩).le

/-- A compact small gauge ball can always be chosen at the scale needed
for the power-prefix estimate. -/
theorem exists_compact_oneParameter_radius [LocallyCompactSpace G] :
    ∃ R : ℝ, 0 < R ∧ (D.constant+1)*R ≤ 1/D.constant ∧
      IsCompact {g : G | D.gauge g ≤ R} := by
  let : MetricSpace G := D.compatibleMetric
  obtain ⟨δ,hδ,hK⟩ := Metric.exists_isCompact_closedBall (1 : G)
  have hC := D.constant_pos
  let R := min δ (1/(D.constant*(D.constant+1)))
  have hR : 0 < R := by dsimp [R]; positivity
  have hscale : (D.constant+1)*R ≤ 1/D.constant := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right δ (1/(D.constant*(D.constant+1)))) (by linarith : 0 ≤ D.constant+1)
    apply hh.trans_eq
    field_simp
  refine ⟨R,hR,hscale,?_⟩
  apply hK.of_isClosed_subset (isClosed_le D.continuous_gauge continuous_const)
  intro g hg
  change D.metric.dist g 1 ≤ δ
  rw [D.metric.dist_comm]
  exact hg.trans (min_le_left _ _)

include D in
/-- The space of actual continuous one-parameter homomorphisms is locally
compact. No vector-space structure is assumed in this argument. -/
theorem oneParameter_locallyCompact [IsTopologicalGroup G] [LocallyCompactSpace G] :
    LocallyCompactSpace (OneParameter G) := by
  let : MetricSpace G := D.compatibleMetric
  obtain ⟨R,hR,hscale,hK⟩ := D.exists_compact_oneParameter_radius
  have hw : WeaklyLocallyCompactSpace (OneParameter G) := by
    constructor
    intro φ
    obtain ⟨T,hT,hφ⟩ := D.oneParameter_exists_window φ (half_pos hR)
    refine ⟨D.oneParameterWindow T R,D.oneParameterWindow_compact hT hR.le hscale hK,?_⟩
    apply D.oneParameterWindow_mem_nhds
    intro t ht
    exact (hφ t ht).trans_lt (half_lt_self hR)
  let := hw
  infer_instance
end GleasonMetricData
end DirectedCycles
