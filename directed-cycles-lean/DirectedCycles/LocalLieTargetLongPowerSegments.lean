module

public import DirectedCycles.LocalToLocalModelPowerLifting
public import DirectedCycles.LocalExponentialRadialLaw
public import Mathlib.Analysis.Normed.Module.RCLike.Real

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] [ChartedSpace E H] {Q : LocalGroupAlgebra H}

/-- A positive-dimensional smooth local model supplies arbitrarily long
nonidentity source power segments. A small nonzero exponential vector
replaces the global connectedness argument. -/
theorem exists_long_power_segment_of_local_lie_model (D : LocalExponentialData (E := E) Q)
    (L : LocalGroupAlgebra G) (A : Set G) (hA : L.one ∈ A)
    (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y)
    (π : LocalGroupHom L Q) (W : Set H) (hW : W ∈ 𝓝 Q.one)
    (hsmall : ∀ x, π.toFun x ∈ W → x ∈ A)
    (hthick : ∀ y ∈ W, ∃ x, π.toFun x = y) (M : ℕ) :
    ∃ z : G, z ≠ L.one ∧ ∀ n ≤ M, L.PowerIn A z n := by
  have hpre : D.chart ⁻¹' W ∈ 𝓝 (0 : E) := by
    apply (D.chart.continuousAt D.zero_mem).preimage_mem_nhds
    simpa only [D.zero] using hW
  obtain ⟨δ,hδ,hδW⟩ := Metric.mem_nhds_iff.mp hpre
  let r := min D.radius δ
  have hr : 0 < r := lt_min D.radius_pos hδ
  let t := r/(2*((M : ℝ)+1))
  have ht : 0 < t := div_pos hr (by positivity)
  obtain ⟨v,hv⟩ := exists_norm_eq (E := E) ht.le
  have hsize : ((M : ℝ)+1)*‖v‖ < r := by
    rw [hv]
    have he : ((M : ℝ)+1)*t = r/2 := by dsimp only [t]; field_simp
    rw [he]
    linarith
  have hvsmall : ‖v‖ < r := by have := (Nat.cast_nonneg M : (0 : ℝ) ≤ M); nlinarith [norm_nonneg v]
  have hvS : v ∈ D.chart.source := D.ball_source (by
    simpa only [Metric.mem_ball,dist_zero_right] using hvsmall.trans_le (min_le_left _ _))
  have hvW : D.chart v ∈ W := hδW (by
    simpa only [Metric.mem_ball,dist_zero_right] using hvsmall.trans_le (min_le_right _ _))
  obtain ⟨z,hz⟩ := hthick (D.chart v) hvW
  have hzA : z ∈ A := hsmall z (hz.symm ▸ hvW)
  have hMsize : (M : ℝ)*‖v‖ < D.radius := by
    have hh := hsize.trans_le (min_le_left _ _)
    nlinarith [norm_nonneg v]
  let q : Q.PowerSegment (π.toFun z) M := {
    power := fun n => D.chart ((n : ℝ) • v)
    product := fun n hn => by
      simpa only [hz] using D.product_replicate v hMsize n hn }
  refine ⟨z,?_,L.powerIn_of_local_model_segment Q A hA hdom π W hsmall hzA M q ?_⟩
  · intro he
    have hcv : D.chart v = D.chart 0 := by rw [D.zero,← hz,he,π.map_one]
    have hv0 : v = 0 := D.chart.injOn hvS D.zero_mem hcv
    have ht0 : t = 0 := by rw [hv0,norm_zero] at hv; exact hv.symm
    exact ht.ne' ht0
  · intro n hn
    change D.chart ((n : ℝ) • v) ∈ W
    apply hδW
    rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hnr : (n : ℝ) ≤ (M : ℝ)+1 := by exact_mod_cast (show n ≤ M+1 by omega)
    exact ((mul_le_mul_of_nonneg_right hnr (norm_nonneg v)).trans_lt hsize).trans_le (min_le_right _ _)
end DirectedCycles
