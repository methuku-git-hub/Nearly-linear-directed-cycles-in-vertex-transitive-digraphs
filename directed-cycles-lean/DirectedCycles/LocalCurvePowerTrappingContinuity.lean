module

public import DirectedCycles.LocalAdditivePowerSegment
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {H : Type*} (Q : LocalGroupAlgebra H)

/-- A local curve law gives all bracketings of every bounded standard power
whose full parameter interval lies inside its multiplication interval. -/
theorem local_curve_product_replicate (f : ℝ → H) (h0 : f 0 = Q.one) {r : ℝ}
    (hadd : ∀ a b : ℝ, |a|+|b| ≤ r → Q.mulRel (f a) (f b) (f (a+b)))
    (t : ℝ) (N : ℕ) (hsize : (N : ℝ)*|t| ≤ r) :
    ∀ n ≤ N, Q.Product (List.replicate n (f t)) (f ((n : ℝ)*t)) := by
  apply Q.product_replicate_of_add (fun n => f ((n : ℝ)*t))
  · simpa only [Nat.cast_zero,zero_mul] using h0
  · intro _; simp only [Nat.cast_one,one_mul]
  · intro n m hnm
    have hh : |(n : ℝ)*t|+|(m : ℝ)*t| ≤ r := by
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
        abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m),← add_mul]
      have hnmr : (n : ℝ)+(m : ℝ) ≤ N := by exact_mod_cast hnm
      exact (mul_le_mul_of_nonneg_right hnmr (abs_nonneg t)).trans hsize
    simpa only [Nat.cast_add,add_mul] using hadd ((n : ℝ)*t) ((m : ℝ)*t) hh

/-- Uniform finite-power trapping makes an actual local multiplicative curve
continuous at zero. The proof needs no global extension of the curve. -/
theorem local_curve_continuousAt_of_power_trapping [TopologicalSpace H]
    (f : ℝ → H) (h0 : f 0 = Q.one) {r : ℝ} (hr : 0 < r)
    (hadd : ∀ a b : ℝ, |a|+|b| ≤ r → Q.mulRel (f a) (f b) (f (a+b)))
    (V : Set H) {s : ℝ} (hs : 0 < s) (hbound : ∀ t : ℝ, |t| ≤ s → f t ∈ V)
    (htrap : ∀ W : Set H, W ∈ 𝓝 Q.one → ∃ N : ℕ, 1 ≤ N ∧
      ∀ x : H, (∀ n ≤ N, Q.PowerIn V x n) → x ∈ W) : ContinuousAt f 0 := by
  have hT : Filter.Tendsto f (𝓝 (0 : ℝ)) (𝓝 Q.one) := by
    apply Filter.tendsto_def.2
    intro W hW
    obtain ⟨N,_,hN⟩ := htrap W hW
    let δ := min r s/((N : ℝ)+1)
    have hδ : 0 < δ := div_pos (lt_min hr hs) (by positivity)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    have htδ : |t| < δ := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht
    have hNt : (N : ℝ)*|t| < min r s := by
      have hh := (lt_div_iff₀ (show 0 < (N : ℝ)+1 by positivity)).1 htδ
      nlinarith [abs_nonneg t]
    apply hN
    intro n hn
    refine ⟨f ((n : ℝ)*t),?_,local_curve_product_replicate Q f h0 hadd t N
      (hNt.le.trans (min_le_left _ _)) n hn⟩
    apply hbound
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hnr : (n : ℝ) ≤ N := by exact_mod_cast hn
    exact (mul_le_mul_of_nonneg_right hnr (abs_nonneg t)).trans
      (hNt.le.trans (min_le_right _ _))
  simpa only [ContinuousAt,h0] using hT
end DirectedCycles
