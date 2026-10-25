module

public import DirectedCycles.GleasonMetricBasics

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- The noncommutative error between a product of powers and the power
of a product is quadratic at the scale on which all factors are small. -/
theorem power_product_distance (g h : G) (n : ℕ) (hn : 0 < n)
    (hsmall : (n : ℝ)*(D.gauge g+D.gauge h) ≤ 1/(8*D.constant)) :
    D.metric.dist (g^n*h^n) ((g*h)^n) ≤
      2*D.constant*(n : ℝ)^2*D.gauge g*D.gauge h := by
  let : MetricSpace G := D.metric
  have hC := D.constant_pos
  have hg0 := D.gauge_nonneg g
  have hh0 := D.gauge_nonneg h
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htwosmall : 2*((n : ℝ)*(D.gauge g+D.gauge h)) ≤ 1/D.constant := by
    have he : 2*(1/(8*D.constant)) ≤ 1/D.constant := by
      have hc8 : 0 < 8*D.constant := by positivity
      rw [mul_one_div]
      apply (div_le_div_iff₀ hc8 hC).2
      linarith
    exact (mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 2)).trans he
  let Z := fun k : ℕ => (g*h)^(n-k)*g^k*h^k
  have hstep : ∀ k < n, D.metric.dist (Z k) (Z (k+1)) ≤
      2*D.constant*(n : ℝ)*D.gauge g*D.gauge h := by
    intro k hk
    have hkr : (k : ℝ) ≤ n := by exact_mod_cast hk.le
    have hkg : D.gauge (g^k) ≤ (n : ℝ)*D.gauge g :=
      (D.gauge_pow_le g k).trans (mul_le_mul_of_nonneg_right hkr hg0)
    have hkh : D.gauge (h^k) ≤ (n : ℝ)*D.gauge h :=
      (D.gauge_pow_le h k).trans (mul_le_mul_of_nonneg_right hkr hh0)
    have hhn : D.gauge h ≤ (n : ℝ)*D.gauge h := by nlinarith
    have hgk0 := D.gauge_nonneg (g^k)
    have hpair : D.gauge (g^k)+D.gauge h ≤ (n : ℝ)*(D.gauge g+D.gauge h) := by nlinarith
    have hkgsmall : D.gauge (g^k) ≤ 1/D.constant := by nlinarith
    have hhsmall : D.gauge h ≤ 1/D.constant := by nlinarith
    have hkhsmall : D.gauge (h^k) ≤ 1/D.constant := by nlinarith
    have hxy : D.metric.dist (h*g^k) (g^k*h) ≤ 1/D.constant := by
      have h0 := D.dist_le_gauges (h*g^k) (g^k*h)
      have h1 := D.gauge_mul_le h (g^k)
      have h2 := D.gauge_mul_le (g^k) h
      nlinarith
    have he1 : Z k = ((g*h)^(n-(k+1))*g)*((h*g^k)*h^k) := by
      dsimp [Z]
      rw [show n-k = n-(k+1)+1 by omega,pow_succ]
      group
    have he2 : Z (k+1) = ((g*h)^(n-(k+1))*g)*((g^k*h)*h^k) := by
      dsimp [Z]
      rw [pow_succ' g k,pow_succ' h k]
      group
    rw [he1,he2,D.left_invariant]
    have hright := D.dist_mul_right_le_two (h*g^k) (g^k*h) (h^k) hxy hkhsmall
    have hswap : D.metric.dist (h*g^k) (g^k*h) ≤ D.constant*D.gauge (g^k)*D.gauge h := by
      rw [D.metric.dist_comm]
      exact D.dist_mul_swap_le (g^k) h hkgsmall hhsmall
    have hbound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkg hC.le) hh0
    nlinarith
  have ht := dist_le_range_sum_dist Z n
  have hsum : (∑ k ∈ Finset.range n, D.metric.dist (Z k) (Z (k+1))) ≤
      (n : ℝ)*(2*D.constant*(n : ℝ)*D.gauge g*D.gauge h) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range n, 2*D.constant*(n : ℝ)*D.gauge g*D.gauge h :=
        Finset.sum_le_sum (fun k hk => hstep k (Finset.mem_range.mp hk))
      _ = _ := by simp
  have hZ0 : Z 0 = (g*h)^n := by simp [Z]
  have hZn : Z n = g^n*h^n := by simp [Z]
  rw [hZ0,hZn,dist_comm] at ht
  exact ht.trans (hsum.trans_eq (by ring))
end GleasonMetricData
end DirectedCycles
