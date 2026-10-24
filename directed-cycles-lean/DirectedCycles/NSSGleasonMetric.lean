import DirectedCycles.LocallyCompactEscapeCommutator
import DirectedCycles.EscapeWordMetricEscape
import DirectedCycles.GleasonYamabeReduction

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
universe u

/-- An actual left-invariant metric on the given topology with the
quantitative escape and commutator estimates used for Lie recognition. -/
structure GleasonMetricData (G : Type u) [Group G] [TopologicalSpace G] where
  metric : MetricSpace G
  topology_eq : metric.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace G)
  left_invariant : ∀ a x y : G, metric.dist (a*x) (a*y) = metric.dist x y
  constant : ℝ
  constant_pos : 0 < constant
  escape : ∀ g : G, ∀ n : ℕ, 0 < n → (n : ℝ)*metric.dist 1 g ≤ 1/constant →
    (n : ℝ)/constant*metric.dist 1 g ≤ metric.dist 1 (g^n)
  commutator : ∀ g h : G, metric.dist 1 g ≤ 1/constant → metric.dist 1 h ≤ 1/constant →
    metric.dist 1 (g⁻¹*h⁻¹*g*h) ≤ constant*metric.dist 1 g*metric.dist 1 h

/-- Every locally compact Hausdorff NSS group admits a genuine Gleason
metric. The supplied topology is preserved exactly; both quantitative
estimates follow from the proved Haar escape constructions. -/
theorem locally_compact_nss_gleason_metric (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (hnss : HasNoSmallSubgroups G) : Nonempty (GleasonMetricData G) := by
  obtain ⟨U,hU,hU1,hUi,hUc,hNSS8⟩ := compact_nss_word_window hnss 8
  have hNSS4 : ∀ x : G, (∀ j : ℕ, x^j ∈ closure (U^4)) → x = 1 := by
    intro x hx
    exact hNSS8 x (fun j => closure_mono (Set.pow_subset_pow_right hU1 (by omega : 4 ≤ 8)) (hx j))
  have hNSS := cyclic_nss_closure_of_fourth hU1 hNSS4
  obtain ⟨D,hD,hprod⟩ := locally_compact_escape_product hU hU1 hUi hUc hNSS4
  obtain ⟨B,hB,hcomm⟩ := locally_compact_escape_commutator hU hU1 hUi hUc hNSS8 hD hprod
  obtain ⟨a,b,ha,hb,hescape⟩ := escapeWordGauge_escape hU hU1 hUc hNSS hD hprod
  obtain ⟨δ,hδ,hball⟩ := escapeWordGauge_ball_subset hU1 hUc hNSS hD hprod hU hU1
  let C := max (1/a) (max (2/δ) (max (1/b) (B*D^2)))
  have hCa : 1/a ≤ C := le_max_left _ _
  have hCδ : 2/δ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCb : 1/b ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCB : B*D^2 ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC : 0 < C := (one_div_pos.mpr ha).trans_le hCa
  have hIa : 1/C ≤ a := by
    simpa only [one_div_one_div] using one_div_le_one_div_of_le (one_div_pos.mpr ha) hCa
  have hIδ : 1/C < δ := by
    have h := one_div_le_one_div_of_le (div_pos (by norm_num : (0 : ℝ) < 2) hδ) hCδ
    have he : 1/(2/δ) = δ/2 := by field_simp
    rw [he] at h
    linarith
  have hIb : 1/C ≤ b := by
    simpa only [one_div_one_div] using one_div_le_one_div_of_le (one_div_pos.mpr hb) hCb
  let m := escapeWordMetric hU hU1 hUi hUc hNSS hD hprod
  have hm : ∀ g : G, m.dist 1 g = escapeWordGauge U g := by
    intro g
    simp only [m,escapeWordMetric_dist,inv_one,one_mul]
  refine ⟨{ metric := m
            topology_eq := escapeWordMetric_topology hU hU1 hUi hUc hNSS hD hprod
            left_invariant := escapeWordMetric_left_invariant hU hU1 hUi hUc hNSS hD hprod
            constant := C
            constant_pos := hC
            escape := ?_
            commutator := ?_ }⟩
  · intro g n hn hsmall
    simp only [hm] at hsmall ⊢
    have h := hescape g n hn (hsmall.trans hIa)
    have hfactor := mul_le_mul_of_nonneg_right hIb
      (mul_nonneg (Nat.cast_nonneg n) (escapeWordGauge_nonneg hU1 g))
    apply le_trans ?_ h
    convert hfactor using 1 <;> ring
  · intro g h hg hh
    simp only [hm] at hg hh ⊢
    have hgu : g ∈ U := hball (hg.trans_lt hIδ)
    have hhu : h ∈ U := hball (hh.trans_lt hIδ)
    have hge := escapeNorm_le_mul_escapeWordGauge hD hprod g
    have hhe := escapeNorm_le_mul_escapeWordGauge hD hprod h
    have hmul : B*escapeNorm U g*escapeNorm U h ≤
        B*(D*escapeWordGauge U g)*(D*escapeWordGauge U h) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hge hB.le
      · exact hhe
      · exact escapeNorm_nonneg hU1 h
      · exact mul_nonneg hB.le (mul_nonneg hD.le (escapeWordGauge_nonneg hU1 g))
    have hcoef := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB
      (escapeWordGauge_nonneg hU1 g)) (escapeWordGauge_nonneg hU1 h)
    exact (escapeWordGauge_le hU1 _).trans ((hcomm g hgu h hhu).trans (hmul.trans (by
      convert hcoef using 1; ring)))

/-- The geometric recognition proposition, separated from construction
of the metric and proved by `gleason_metric_lie_recognition` in
`GleasonMetricLieStructure`. -/
def GleasonMetricLieRecognition : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G],
    Nonempty (GleasonMetricData G) → HasFiniteDimensionalLieStructure G

theorem nss_lie_recognition_of_gleason_metric
    (hgeom : GleasonMetricLieRecognition.{u}) : LocallyCompactNSSLieRecognition.{u} := by
  intro G _ _ _ _ _ hnss
  exact hgeom G (locally_compact_nss_gleason_metric G hnss)
end DirectedCycles
