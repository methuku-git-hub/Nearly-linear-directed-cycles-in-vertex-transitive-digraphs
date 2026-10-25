module

public import DirectedCycles.GleasonNearestPointContradiction
public import DirectedCycles.CompactNearestResidual
public import DirectedCycles.CompactRoundedPowerLimit
public import DirectedCycles.NormalizedPowerScale
public import Mathlib.Topology.Sequences

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace GleasonLieAlgebra
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- The image of a compact identity neighbourhood on which evaluation is
injective contains an identity neighbourhood in the group. The nearest-point
contradiction constructs all normalised scales and limiting curves. -/
theorem compact_exp_image_mem_nhds {K : Set (GleasonLieAlgebra D)}
    (hK : IsCompact K) (hKnhds : K ∈ 𝓝 0) (hinj : Set.InjOn (exp D) K) :
    exp D '' K ∈ 𝓝 (1 : G) := by
  let : MetricSpace G := D.compatibleMetric
  classical
  by_contra hn
  let V := exp D '' K
  have hV : IsCompact V := hK.image (continuous_exp D)
  have hK0 : (0 : GleasonLieAlgebra D) ∈ K := mem_of_mem_nhds hKnhds
  have hV1 : (1 : G) ∈ V := ⟨0,hK0,exp_zero D⟩
  have hclosure : (1 : G) ∈ closure Vᶜ := by
    rw [closure_compl]
    exact fun h => hn (mem_interior_iff_mem_nhds.mp h)
  obtain ⟨g,hgo,hg⟩ := mem_closure_iff_seq_limit.mp hclosure
  obtain ⟨h,k,hprops,hh,hk⟩ := D.exists_compact_nearest_residual hV hV1 g hgo hg
  have hlift : ∀ i : ℕ, ∃ x ∈ K, exp D x = h i := fun i => (hprops i).1
  choose x hx hexp using hlift
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hxlim : Tendsto x (U : Filter ℕ) (𝓝 0) := by
    apply compact_exp_lift_tendsto_zero D U hK hK0 hinj x (Filter.Eventually.of_forall hx)
    have he : (fun i => exp D (x i)) = h := funext hexp
    rw [he]
    exact hh.mono_left hU
  have hkpos : ∀ i : ℕ, 0 < D.gauge (k i) := by
    intro i
    have hne : D.gauge (k i) ≠ 0 := fun he => (hprops i).2.2.1 ((D.gauge_eq_zero_iff _).mp he)
    exact lt_of_le_of_ne (D.gauge_nonneg _) hne.symm
  have hkzero : Tendsto (fun i => D.gauge (k i)) (U : Filter ℕ) (𝓝 (0 : ℝ)) := by
    simpa only [D.gauge_one,Function.comp_def] using D.continuous_gauge.tendsto 1 |>.comp (hk.mono_left hU)
  obtain ⟨r₀,hr₀,hp₀⟩ := D.exists_power_distance_radius
  have hC := D.constant_pos
  let r := min r₀ (1/(8*D.constant))
  have hrpos : 0 < r := lt_min hr₀ (by positivity)
  have hr : r ≤ 1/(8*D.constant) := min_le_right _ _
  have hp : ∀ a b : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge a ≤ r → (n : ℝ)*D.gauge b ≤ r →
      (n : ℝ)/(2*D.constant)*D.metric.dist a b ≤ D.metric.dist (a^n) (b^n) ∧
      D.metric.dist (a^n) (b^n) ≤ 2*(n : ℝ)*D.metric.dist a b := by
    intro a b n hn ha hb
    exact hp₀ a b n hn (ha.trans (min_le_left _ _)) (hb.trans (min_le_left _ _))
  obtain ⟨δ,hδ,hδK⟩ := Metric.exists_isCompact_closedBall (1 : G)
  let R := min (r/2) (δ/2)
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hRr : R ≤ r := by have := min_le_left (r/2) (δ/2); linarith
  have hKR : IsCompact {z : G | D.gauge z ≤ 2*R} := by
    apply hδK.of_isClosed_subset (isClosed_le D.continuous_gauge continuous_const)
    intro z hz
    change D.metric.dist z 1 ≤ δ
    rw [D.metric.dist_comm]
    have hRδ := min_le_right (r/2) (δ/2)
    exact hz.trans (by linarith)
  let N : ℕ → ℕ := fun i => ⌊R/D.gauge (k i)⌋₊
  have hsmall : ∀ᶠ i in (U : Filter ℕ), D.gauge (k i) ≤ R/2 :=
    (hkzero.eventually (gt_mem_nhds (half_pos hR))).mono fun _ h => h.le
  have hscale : ∀ᶠ i in (U : Filter ℕ), 0 < N i ∧ R/2 ≤ (N i : ℝ)*D.gauge (k i) ∧ (N i : ℝ)*D.gauge (k i) ≤ R :=
    hsmall.mono fun i hi => normalized_power_scale_bounds hR (hkpos i) hi
  have hNt : Tendsto N (U : Filter ℕ) atTop := normalized_power_scale_tendsto hR (Filter.Eventually.of_forall hkpos) hkzero
  obtain ⟨φ,hφ,hφlim⟩ := D.exists_rounded_power_limit U k N hR.le
    (hscale.mono fun _ h => ⟨h.1,h.2.2⟩) (hk.mono_left hU) hKR
  let v : GleasonLieAlgebra D := φ
  have hlink : ∀ᶠ i in (U : Filter ℕ), g i = exp D (x i)*k i := by
    apply Filter.Eventually.of_forall
    intro i
    rw [hexp i,(hprops i).2.1]
    simp
  have hmin : ∀ᶠ i in (U : Filter ℕ), ∀ y ∈ K, D.gauge (k i) ≤ D.metric.dist (g i) (exp D y) := by
    apply Filter.Eventually.of_forall
    intro i y hy
    exact (hprops i).2.2.2.2.2 _ ⟨y,hy,rfl⟩
  have hlimit : Tendsto (fun i => (k i)^(N i)) (U : Filter ℕ) (𝓝 (exp D v)) := by
    change Tendsto (fun i => (k i)^(N i)) (U : Filter ℕ) (𝓝 (φ.eval 1))
    simpa only [roundedPower_one] using hφlim 1 (by norm_num)
  exact no_nearest_normalized_power_family D hKnhds hrpos hR hRr hr hp
    g k x N hxlim hNt hlink hmin hscale v hφ hlimit

/-- Evaluation sends every neighbourhood of zero in the constructed curve
space to a neighbourhood of the identity in the group. -/
theorem exp_image_mem_nhds {V : Set (GleasonLieAlgebra D)} (hV : V ∈ 𝓝 0) :
    exp D '' V ∈ 𝓝 (1 : G) := by
  obtain ⟨U,hU,hinj⟩ := exp_locally_injective D
  obtain ⟨K,hKnhds,hKsub,hK⟩ := local_compact_nhds (Filter.inter_mem hV hU)
  have hKV : K ⊆ V := fun _ hx => (hKsub hx).1
  have hKU : K ⊆ U := fun _ hx => (hKsub hx).2
  exact Filter.mem_of_superset (compact_exp_image_mem_nhds D hK hKnhds (hinj.mono hKU))
    (Set.image_mono hKV)
end GleasonLieAlgebra
end DirectedCycles
