import DirectedCycles.GleasonMetricBasics
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles.GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- Compare two actual paths by their left increments. Only suffixes of
one path enter the uniform translation bound. -/
theorem increment_comparison (a b : ℕ → G) (n : ℕ)
    (ha : a 0 = 1) (hb : b 0 = 1)
    (hstep : ∀ k < n, D.metric.dist ((a k)⁻¹*a (k+1)) ((b k)⁻¹*b (k+1)) ≤ 1/D.constant)
    (hsuffix : ∀ k ≤ n, D.gauge ((b k)⁻¹*b n) ≤ 1/D.constant) :
    D.metric.dist (a n) (b n) ≤
      2*∑ k ∈ Finset.range n, D.metric.dist ((a k)⁻¹*a (k+1)) ((b k)⁻¹*b (k+1)) := by
  let : MetricSpace G := D.metric
  let z (k : ℕ) := a k*((b k)⁻¹*b n)
  have h0 : z 0 = b n := by simp [z,ha,hb]
  have hn : z n = a n := by simp [z]
  have hdist (k : ℕ) (hk : k < n) : dist (z k) (z (k+1)) ≤
      2*D.metric.dist ((a k)⁻¹*a (k+1)) ((b k)⁻¹*b (k+1)) := by
    let u := (a k)⁻¹*a (k+1)
    let v := (b k)⁻¹*b (k+1)
    let s := (b (k+1))⁻¹*b n
    have he₁ : z k = a k*(v*s) := by dsimp [z,v,s]; group
    have he₂ : z (k+1) = a k*(u*s) := by dsimp [z,u,s]; group
    rw [he₁,he₂]
    change D.metric.dist (a k*(v*s)) (a k*(u*s)) ≤ _
    rw [D.left_invariant,D.metric.dist_comm (v*s) (u*s)]
    exact D.dist_mul_right_le_two u v s (hstep k hk) (hsuffix (k+1) (by omega))
  have h := dist_le_range_sum_of_dist_le (f := z) n (fun {k} hk => hdist k hk)
  rw [h0,hn,dist_comm] at h
  exact h.trans_eq (Finset.mul_sum ..).symm

end DirectedCycles.GleasonMetricData
