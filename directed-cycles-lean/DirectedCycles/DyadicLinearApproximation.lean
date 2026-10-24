import DirectedCycles.DyadicCurveAdditivity
import DirectedCycles.LocalAdditiveCurveLinear

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuous curve with quadratic local addition error and a contracting
dyadic coordinate has a real linear approximation with quadratic error in
the curve norm. This is an analytic step toward one-parameter regularity. -/
theorem exists_dyadic_linear_approximation (f : ℝ → E) (h0 : f 0 = 0)
    (hcont : ContinuousAt f 0) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hc : ∀ t : ℝ, |t| ≤ r → ‖f (t/2)‖ ≤ (2/3)*‖f t‖)
    (ha : ∀ s t : ℝ, |s|+|t| ≤ r → ‖f (s+t)-f s-f t‖ ≤ C*(‖f s‖+‖f t‖)^2) :
    ∃ v : E, ∀ t : ℝ, |t| ≤ r → ‖f t-t • v‖ ≤ 16*C*‖f t‖^2 := by
  classical
  have he : ∀ t : ℝ, |t| ≤ r → ‖f t-(2 : ℝ) • f (t/2)‖ ≤ (4*C)*‖f (t/2)‖^2 := by
    intro t ht
    have ht' : |t/2|+|t/2| ≤ r := by rw [abs_div]; norm_num; linarith
    calc
      ‖f t-(2 : ℝ) • f (t/2)‖ = ‖f (t/2+t/2)-f (t/2)-f (t/2)‖ := by
        rw [show t/2+t/2=t by ring,two_smul]
        congr 1
        abel
      _ ≤ C*(‖f (t/2)‖+‖f (t/2)‖)^2 := ha _ _ ht'
      _ = (4*C)*‖f (t/2)‖^2 := by ring
  have hex : ∀ t : ℝ, |t| ≤ r → ∃ v : E,
      Filter.Tendsto (dyadicCurve f t) Filter.atTop (𝓝 v) ∧ ‖v-f t‖ ≤ 16*C*‖f t‖^2 := by
    intro t ht
    obtain ⟨v,hv,hb⟩ := exists_dyadic_curve_limit f (by positivity : 0 ≤ 4*C) hc he ht
    exact ⟨v,hv,by convert hb using 1; ring⟩
  let g : ℝ → E := fun t => if ht : |t| ≤ r then Classical.choose (hex t ht) else 0
  have hspec : ∀ t : ℝ, |t| ≤ r →
      Filter.Tendsto (dyadicCurve f t) Filter.atTop (𝓝 (g t)) ∧ ‖g t-f t‖ ≤ 16*C*‖f t‖^2 := by
    intro t ht
    dsimp only [g]
    rw [dite_eq_left ht]
    exact Classical.choose_spec (hex t ht)
  have hg0 : g 0 = 0 := by
    have hb := (hspec 0 (by simpa using hr.le)).2
    simpa only [h0,sub_zero,norm_zero,zero_pow (by omega : 2 ≠ 0),mul_zero,norm_le_zero_iff] using hb
  have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |t| ≤ r := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
    have hh : |t| < r := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht
    exact hh.le
  have hbound : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ‖g t‖ ≤ ‖f t‖+16*C*‖f t‖^2 := by
    filter_upwards [hnear] with t ht
    have hh := norm_add_le (g t-f t) (f t)
    rw [sub_add_cancel] at hh
    linarith [(hspec t ht).2]
  have hn : Filter.Tendsto (fun t => ‖f t‖) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [h0,norm_zero] using hcont.norm.tendsto
  have hgcont : ContinuousAt g 0 := by
    have hu := hn.add ((hn.pow 2).const_mul (16*C))
    have hu' : Filter.Tendsto (fun t => ‖f t‖+16*C*‖f t‖^2) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa only [zero_pow (by omega : 2 ≠ 0),mul_zero,zero_add] using hu
    have hz : Filter.Tendsto g (𝓝 (0 : ℝ)) (𝓝 0) := squeeze_zero_norm' hbound hu'
    simpa only [ContinuousAt,hg0] using hz
  obtain ⟨v,hv⟩ := local_additive_curve_linear g hg0 hgcont hr
    (fun s t ht => dyadic_curve_limit_add f g hC hc ha (fun t ht => (hspec t ht).1) ht)
  refine ⟨v,?_⟩
  intro t ht
  rw [← hv t ht,norm_sub_rev]
  exact (hspec t ht).2
end DirectedCycles
