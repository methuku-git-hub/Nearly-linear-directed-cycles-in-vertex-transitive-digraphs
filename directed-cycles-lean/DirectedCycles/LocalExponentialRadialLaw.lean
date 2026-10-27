module

public import DirectedCycles.SmoothLocalExponentialChart
public import DirectedCycles.LocalAdditivePowerSegment

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
namespace LocalExponentialData
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] {L : LocalGroupAlgebra G} (D : LocalExponentialData (E := E) L)

/-- The unit radial law rescales to any segment whose total coordinate length
stays inside the constructed exponential radius. -/
theorem radial_of_norm (v : E) (s t : ℝ) (hsize : (|s|+|t|)*‖v‖ < D.radius) :
    L.mulRel (D.chart (s • v)) (D.chart (t • v)) (D.chart ((s+t) • v)) := by
  let a := |s|+|t|
  have ha : 0 ≤ a := add_nonneg (abs_nonneg s) (abs_nonneg t)
  by_cases ha0 : a = 0
  · have hs : s = 0 := abs_eq_zero.mp (by dsimp only [a] at ha0; linarith [abs_nonneg s,abs_nonneg t])
    have ht : t = 0 := abs_eq_zero.mp (by dsimp only [a] at ha0; linarith [abs_nonneg s,abs_nonneg t])
    simpa only [hs,ht,zero_add,zero_smul,D.zero] using L.one_mul L.one
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hv : ‖a • v‖ < D.radius := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hap] using hsize
  have habs : |s/a|+|t/a| ≤ 1 := by
    rw [abs_div,abs_div,abs_of_pos hap,← add_div]
    change a/a ≤ 1
    rw [div_self ha0]
  have h := D.radial (a • v) hv (s/a) (t/a) habs
  simpa only [smul_smul,← add_div,div_mul_cancel₀ _ ha0] using h

/-- Inversion is exact in the symmetric half-radius exponential chart. -/
theorem inv_chart {v : E} (hv : 2*‖v‖ < D.radius) : D.chart (-v) = L.inv (D.chart v) := by
  have h := D.radial_of_norm v 1 (-1) (by norm_num; exact hv)
  have he : L.mulRel (D.chart v) (D.chart (-v)) L.one := by
    simpa only [one_smul,neg_one_smul,add_neg_cancel,zero_smul,D.zero] using h
  exact L.right_inverse_unique he

/-- All bracketings of bounded radial powers are certified in the local
group, with exactly the expected natural multiple coordinate. -/
theorem product_replicate {N : ℕ} (v : E) (hsize : (N : ℝ)*‖v‖ < D.radius) :
    ∀ n ≤ N, L.Product (List.replicate n (D.chart v)) (D.chart ((n : ℝ) • v)) := by
  apply L.product_replicate_of_add (fun n => D.chart ((n : ℝ) • v))
  · simpa only [Nat.cast_zero,zero_smul] using D.zero
  · intro _; simp only [Nat.cast_one,one_smul]
  · intro n m hnm
    have hbound : ((n : ℝ)+(m : ℝ))*‖v‖ < D.radius := by
      have hle : (n : ℝ)+(m : ℝ) ≤ N := by exact_mod_cast hnm
      exact (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans_lt hsize
    have hh := D.radial_of_norm v n m (by
      simpa only [abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n),abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)] using hbound)
    simpa only [Nat.cast_add] using hh
end LocalExponentialData
end DirectedCycles
