import DirectedCycles.GleasonMetricTopology
import DirectedCycles.NormalizedPowerScale
import DirectedCycles.NormedAlgebraPowerPrefix

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonMetricData
variable {G A : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [NormedRing A] [NormedAlgebra ℝ A]

/-- Any continuous homomorphism into a normed algebra is locally bounded
linearly by the source gauge. A long small power prefix proves the bound. -/
theorem continuous_hom_gauge_bound (F : ContinuousMonoidHom G A) :
    ∃ L r : ℝ, 0 < L ∧ 0 < r ∧ ∀ g : G,
      D.gauge g ≤ r → ‖F g-1‖ ≤ L*D.gauge g := by
  let : MetricSpace G := D.compatibleMetric
  have hc : Continuous (fun g : G => ‖F g-1‖) := (F.continuous.sub continuous_const).norm
  have hnear : ∀ᶠ g : G in 𝓝 1, ‖F g-1‖ < 1/4 := by
    have h0 : ‖F (1 : G)-1‖ < (1 : ℝ)/4 := by simp
    exact (hc.tendsto 1).eventually (gt_mem_nhds h0)
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp hnear
  let R := δ/2
  have hR : 0 < R := half_pos hδ
  refine ⟨2/R,R/2,by positivity,half_pos hR,?_⟩
  intro g hg
  by_cases hg1 : g = 1
  · subst g
    simp only [map_one,sub_self,norm_zero,D.gauge_one,mul_zero,le_refl]
  have hgpos : 0 < D.gauge g := lt_of_le_of_ne (D.gauge_nonneg g)
    (fun hz => hg1 ((D.gauge_eq_zero_iff g).mp hz.symm))
  let N : ℕ := ⌊R/D.gauge g⌋₊
  have hscale := normalized_power_scale_bounds hR hgpos hg
  change 0 < N ∧ R/2 ≤ (N : ℝ)*D.gauge g ∧ (N : ℝ)*D.gauge g ≤ R at hscale
  have hprefix : ∀ k ≤ N, ‖(F g)^k-1‖ ≤ (1 : ℝ)/4 := by
    intro k hk
    rw [← map_pow]
    have hkball : g^k ∈ Metric.ball (1 : G) δ := by
      rw [Metric.mem_ball,D.metric.dist_comm]
      change D.gauge (g^k) < δ
      have hkR : (k : ℝ) ≤ N := by exact_mod_cast hk
      exact (D.gauge_pow_le g k).trans_lt
        ((mul_le_mul_of_nonneg_right hkR hgpos.le).trans hscale.2.2 |>.trans_lt (by dsimp [R]; linarith))
    exact (hδb hkball).le
  have hb := normedAlgebra_power_prefix_bound (F g) (1/4) (by norm_num) (by norm_num) N hprefix
  have hN : (N : ℝ)*‖F g-1‖ ≤ 1 := by linarith
  have h₁ := mul_le_mul_of_nonneg_right hscale.2.1 (norm_nonneg (F g-1))
  have h₂ := mul_le_mul_of_nonneg_right hN hgpos.le
  have heq : 2/R*D.gauge g = (2*D.gauge g)/R := by ring
  rw [heq]
  apply (le_div_iff₀ hR).mpr
  nlinarith

end DirectedCycles.GleasonMetricData
