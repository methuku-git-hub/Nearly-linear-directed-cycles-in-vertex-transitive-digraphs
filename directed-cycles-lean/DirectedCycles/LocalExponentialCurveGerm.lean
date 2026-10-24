import DirectedCycles.SmoothLocalCoordinateLawAtIdentity
import DirectedCycles.LocalRelationCurveCoordinates
import DirectedCycles.LocalRelationCurveGermUniqueness
import DirectedCycles.LocalMultiplicativeCurveDerivative
import DirectedCycles.LocalMultiplicativeCurveUniqueness
import DirectedCycles.LocalExponentialRadialLaw

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
namespace LocalExponentialData
variable {H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [ChartedSpace E H] {Q : LocalGroupAlgebra H}
    (D : LocalExponentialData (E := E) Q)

/-- Every continuous actual local curve agrees near zero with the radial
curve of its tangent in the constructed exponential coordinates. -/
theorem curve_germ (hQ : LocalGroupSmoothness (E := E) Q)
    (f : ℝ → H) (hf0 : f 0 = Q.one) (hfc : ContinuousAt f 0)
    (hfadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t))) :
    ∃ v : E, HasDerivAt (fun t => D.baseChart.symm (f t)) v 0 ∧
      f =ᶠ[𝓝 (0 : ℝ)] (fun t => D.chart (t • v)) := by
  obtain ⟨μ,hμ0,hμ,hrel,hl,hr,_⟩ := smooth_local_coordinate_law_at_identity Q hQ
    D.baseChart D.base_zero_mem D.base_zero D.base_smooth D.base_inverse_smooth
  obtain ⟨hc0,hcc,r,hr0,hclaw⟩ := local_relation_curve_coordinate_law Q D.baseChart
    D.base_zero_mem D.base_zero μ hμ0 hμ.continuousAt hrel f hf0 hfc (by norm_num : (0 : ℝ)<1) hfadd
  obtain ⟨v,hv⟩ := local_multiplicative_curve_hasDerivAt μ (hμ.of_le (by simp)) hl hr
    (fun t => D.baseChart.symm (f t)) hc0 hcc hr0 hclaw
  let g : ℝ → H := fun t => D.chart (t • v)
  have htv : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [one_smul,id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hFv : HasDerivAt (fun t : ℝ => D.coordinateMap (t • v)) v 0 := by
    have hD : HasFDerivAt D.coordinateMap (ContinuousLinearMap.id ℝ E) ((0 : ℝ) • v) := by
      simpa only [zero_smul] using D.coordinate_derivative.hasFDerivAt
    have hh := hD.comp_hasDerivAt 0 htv
    simpa only [zero_smul,ContinuousLinearMap.id_apply,Function.comp_def] using hh
  have hFT : Filter.Tendsto (fun t : ℝ => D.coordinateMap (t • v)) (𝓝 0) (𝓝 (0 : E)) := by
    simpa only [zero_smul,D.coordinate_zero] using hFv.continuousAt.tendsto
  have hcg : (fun t : ℝ => D.baseChart.symm (g t)) =ᶠ[𝓝 0]
      (fun t => D.coordinateMap (t • v)) := by
    filter_upwards [hFT.eventually (D.baseChart.open_source.mem_nhds D.base_zero_mem)] with t ht
    change D.baseChart.symm (D.chart (t • v)) = _
    rw [D.chart_eq,D.baseChart.left_inv ht]
  have hgv : HasDerivAt (fun t => D.baseChart.symm (g t)) v 0 := hFv.congr_of_eventuallyEq hcg
  have hg0 : g 0 = Q.one := by simp only [g,zero_smul,D.zero]
  have hgc : ContinuousAt g 0 := by
    have hT : Filter.Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : E)) := by
      simpa only [zero_smul] using htv.continuousAt.tendsto
    change Filter.Tendsto (fun t => D.chart (t • v)) (𝓝 0) (𝓝 (D.chart ((0 : ℝ) • v)))
    rw [zero_smul]
    exact (D.chart.continuousAt D.zero_mem).tendsto.comp hT
  let s : ℝ := D.radius/(‖v‖+1)/2
  have hs : 0 < s := div_pos (div_pos D.radius_pos (by positivity)) (by norm_num)
  have hsn : s*‖v‖ < D.radius := by
    have he : s*(‖v‖+1)*2 = D.radius := by dsimp only [s]; field_simp
    nlinarith [norm_nonneg v,D.radius_pos]
  have hglaw : ∀ a b : ℝ, |a|+|b| ≤ s → Q.mulRel (g a) (g b) (g (a+b)) := by
    intro a b hab
    exact D.radial_of_norm v a b ((mul_le_mul_of_nonneg_right hab (norm_nonneg v)).trans_lt hsn)
  obtain ⟨hcg0,_,s',hs',hcglaw⟩ := local_relation_curve_coordinate_law Q D.baseChart
    D.base_zero_mem D.base_zero μ hμ0 hμ.continuousAt hrel g hg0 hgc hs hglaw
  have heq := local_multiplicative_curve_eventually_unique μ (hμ.of_le (by simp))
    (fun t => D.baseChart.symm (f t)) (fun t => D.baseChart.symm (g t))
    hc0 hcg0 hv hgv hr0 hs' hclaw hcglaw
  have htarget : Q.one ∈ D.baseChart.target := D.base_zero ▸ D.baseChart.mapsTo D.base_zero_mem
  have hfT : Filter.Tendsto f (𝓝 0) (𝓝 Q.one) := by simpa only [hf0] using hfc.tendsto
  have hgT : Filter.Tendsto g (𝓝 0) (𝓝 Q.one) := by simpa only [hg0] using hgc.tendsto
  refine ⟨v,hv,?_⟩
  filter_upwards [heq,hfT.eventually (D.baseChart.open_target.mem_nhds htarget),
    hgT.eventually (D.baseChart.open_target.mem_nhds htarget)] with t he hf hg
  exact D.baseChart.symm.injOn hf hg he

omit [CompleteSpace E] in
/-- The radial agreement holds at every parameter where both the actual
curve law and the constructed exponential radius apply. -/
theorem curve_eq_of_germ (f : ℝ → H) (hf0 : f 0 = Q.one)
    (hfadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t)))
    (v : E) (hnear : f =ᶠ[𝓝 (0 : ℝ)] (fun t => D.chart (t • v)))
    (t : ℝ) (ht : |t| ≤ 1) (htv : |t| * ‖v‖ < D.radius) : f t = D.chart (t • v) := by
  apply local_relation_curve_eq_of_eventually_eq Q f (fun t => D.chart (t • v))
    (by simpa only [zero_smul,D.zero] using hf0) hfadd (s := |t|) _ hnear t ht le_rfl
  intro a b hab
  exact D.radial_of_norm v a b ((mul_le_mul_of_nonneg_right hab (norm_nonneg v)).trans_lt htv)
end LocalExponentialData
end DirectedCycles
