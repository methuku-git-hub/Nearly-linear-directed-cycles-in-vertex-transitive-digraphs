import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A quantitative left-endpoint quadrature estimate on a subinterval. -/
theorem lipschitz_interval_quadrature {f : ℝ → E} {L : NNReal}
    (hf : LipschitzOnWith L f (Set.Icc 0 1)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ‖(b-a) • f a-∫ t in a..b, f t‖ ≤ (L : ℝ)*(b-a)^2 := by
  have hc : ContinuousOn f (Set.uIcc a b) := hf.continuousOn.mono (by
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact ⟨ha.trans ht.1,ht.2.trans hb⟩)
  have he : (b-a) • f a-∫ t in a..b, f t = ∫ t in a..b, f a-f t := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hc.intervalIntegrable,
      intervalIntegral.integral_const]
  rw [he]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := (L : ℝ)*(b-a)) (f := fun t => f a-f t) (by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht0 : 0 ≤ t := ha.trans ht.1.le
      have ht1 : t ≤ 1 := ht.2.trans hb
      have hl := hf.norm_sub_le (show a ∈ Set.Icc 0 1 from ⟨ha,hab.trans hb⟩) ⟨ht0,ht1⟩
      rw [Real.norm_eq_abs,abs_of_nonpos (by linarith [ht.1] : a-t ≤ 0)] at hl
      exact hl.trans (mul_le_mul_of_nonneg_left (by linarith [ht.2]) L.coe_nonneg))
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
  exact h.trans_eq (by ring)

/-- The uniform left-endpoint Riemann sum has error at most `L/n`.
The integral is the actual vector-valued interval integral. -/
theorem lipschitz_riemann_sum_error {f : ℝ → E} {L : NNReal}
    (hf : LipschitzOnWith L f (Set.Icc 0 1)) (n : ℕ) (hn : 0 < n) :
    ‖(1/(n : ℝ)) • (∑ k ∈ Finset.range n, f ((k : ℝ)/n)) - ∫ t in (0 : ℝ)..1, f t‖ ≤
      (L : ℝ)/n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let a (k : ℕ) : ℝ := (k : ℝ)/n
  have hab (k : ℕ) : a k ≤ a (k+1) := by dsimp [a]; exact div_le_div_of_nonneg_right (by push_cast; linarith) hnR.le
  have h0 (k : ℕ) : 0 ≤ a k := by dsimp [a]; positivity
  have h1 (k : ℕ) (hk : k ≤ n) : a k ≤ 1 := by
    dsimp [a]
    exact (div_le_one hnR).mpr (by exact_mod_cast hk)
  have hδ (k : ℕ) : a (k+1)-a k = 1/(n : ℝ) := by dsimp [a]; push_cast; ring
  have hint (k : ℕ) (hk : k < n) : IntervalIntegrable f MeasureTheory.volume (a k) (a (k+1)) := by
    apply ContinuousOn.intervalIntegrable
    apply hf.continuousOn.mono
    rw [Set.uIcc_of_le (hab k)]
    intro t ht
    exact ⟨(h0 k).trans ht.1,ht.2.trans (h1 (k+1) (by omega))⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : a 0 = 0 := by simp [a]
  have han : a n = 1 := by simp [a,ne_of_gt hnR]
  rw [ha0,han] at hsum
  have he : (1/(n : ℝ)) • (∑ k ∈ Finset.range n, f (a k)) - ∫ t in (0 : ℝ)..1, f t =
      ∑ k ∈ Finset.range n, ((a (k+1)-a k) • f (a k)-∫ t in a k..a (k+1), f t) := by
    rw [Finset.sum_sub_distrib,hsum,Finset.smul_sum]
    simp only [hδ]
  change ‖(1/(n : ℝ)) • (∑ k ∈ Finset.range n, f (a k)) - ∫ t in (0 : ℝ)..1, f t‖ ≤ _
  rw [he]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ => (L : ℝ)*(1/(n : ℝ))^2) (fun k hk => ?_)).trans ?_)
  · have h := lipschitz_interval_quadrature hf (h0 k) (hab k) (h1 (k+1) (by have := Finset.mem_range.mp hk; omega))
    rw [hδ] at h
    simpa only [hδ] using h
  · simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    exact le_of_eq (by field_simp)

/-- Uniform Riemann sums of a locally Lipschitz curve converge to its
Bochner integral on the unit interval. -/
theorem lipschitz_riemann_sum_tendsto {f : ℝ → E} {L : NNReal}
    (hf : LipschitzOnWith L f (Set.Icc 0 1)) :
    Tendsto (fun n : ℕ => (1/(n : ℝ)) • (∑ k ∈ Finset.range n, f ((k : ℝ)/n))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  have hb : ∀ᶠ n : ℕ in atTop,
      ‖(1/(n : ℝ)) • (∑ k ∈ Finset.range n, f ((k : ℝ)/n)) - ∫ t in (0 : ℝ)..1, f t‖ ≤ (L : ℝ)/n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact lipschitz_riemann_sum_error hf n hn
  have ht : Tendsto (fun n : ℕ => (L : ℝ)/n) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (L : ℝ)
  have h := squeeze_zero_norm' hb ht
  simpa only [sub_add_cancel,zero_add] using h.add_const (∫ t in (0 : ℝ)..1, f t)

end DirectedCycles
