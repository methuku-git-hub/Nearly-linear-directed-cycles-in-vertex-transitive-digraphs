import DirectedCycles.GleasonIncrementComparison

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles.GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- Replace the elementary factor in the exact conjugate decomposition of
`g^n*h^n`. The total error is linear in the number of factors. -/
theorem power_product_conjugate_approximation (g h u : G) (n : ℕ)
    (hsmall : 2*(n : ℝ)*(D.gauge g+D.gauge h) ≤ 1/D.constant)
    (herr : 2*D.metric.dist (g*h) u ≤ 1/D.constant) :
    D.metric.dist (g^n*h^n)
      (((List.range n).map (fun k => (h^k)⁻¹*u*h^k)).prod) ≤
      4*(n : ℝ)*D.metric.dist (g*h) u := by
  let a (k : ℕ) := ((List.range k).map (fun j => (h^j)⁻¹*u*h^j)).prod
  let b (k : ℕ) := g^k*h^k
  have hd : 0 ≤ D.metric.dist (g*h) u := by let : MetricSpace G := D.metric; exact dist_nonneg
  have hnon : 0 ≤ D.gauge g+D.gauge h := add_nonneg (D.gauge_nonneg _) (D.gauge_nonneg _)
  have hprefix (k : ℕ) (hk : k ≤ n) : D.gauge (h^k) ≤ 1/D.constant := by
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
    have hpw := D.gauge_pow_le h k
    have h₁ : (k : ℝ)*D.gauge h ≤ (n : ℝ)*(D.gauge g+D.gauge h) :=
      (mul_le_mul_of_nonneg_right hkn (D.gauge_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (D.gauge_nonneg _)) (by positivity))
    exact hpw.trans (h₁.trans (by nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) by positivity) hnon]))
  have ha (k : ℕ) : (a k)⁻¹*a (k+1) = (h^k)⁻¹*u*h^k := by
    dsimp [a]
    rw [List.prod_range_succ]
    group
  have hb (k : ℕ) : (b k)⁻¹*b (k+1) = (h^k)⁻¹*(g*h)*h^k := by
    dsimp [b]
    rw [pow_succ,pow_succ']
    group
  have hstep (k : ℕ) (hk : k < n) :
      D.metric.dist ((a k)⁻¹*a (k+1)) ((b k)⁻¹*b (k+1)) ≤ 2*D.metric.dist (g*h) u := by
    rw [ha,hb]
    simp only [mul_assoc]
    rw [D.left_invariant,D.metric.dist_comm]
    simpa only [mul_assoc] using
      D.dist_mul_right_le_two (g*h) u (h^k) (by linarith) (hprefix k (by omega))
  have htail (k : ℕ) (hk : k ≤ n) : D.gauge ((b k)⁻¹*b n) ≤ 1/D.constant := by
    have hbnd (j : ℕ) : D.gauge (b j) ≤ (j : ℝ)*(D.gauge g+D.gauge h) := by
      exact (D.gauge_mul_le _ _).trans ((add_le_add (D.gauge_pow_le g j) (D.gauge_pow_le h j)).trans_eq (by ring))
    have h := D.gauge_mul_le ((b k)⁻¹) (b n)
    rw [D.gauge_inv] at h
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
    have hkn' := mul_le_mul_of_nonneg_right hkn hnon
    exact (h.trans (add_le_add (hbnd k) (hbnd n))).trans (by nlinarith)
  have hc := D.increment_comparison a b n (by simp [a]) (by simp [b])
    (fun k hk => (hstep k hk).trans herr) htail
  have hs := Finset.sum_le_sum (fun k hk => hstep k (Finset.mem_range.mp hk))
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  rw [D.metric.dist_comm] at hc
  exact hc.trans ((mul_le_mul_of_nonneg_left hs (by norm_num)).trans_eq (by ring))

end DirectedCycles.GleasonMetricData
