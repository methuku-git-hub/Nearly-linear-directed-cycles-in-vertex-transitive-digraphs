import DirectedCycles.GleasonIncrementComparison

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles.GleasonMetricData
variable {G E : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [NormedAddCommGroup E]

/-- A quadratic local product error gives a quadratic error for every
finite ordered product, with a bound independent of the number of factors. -/
theorem approximate_product (F : E → G) (hF0 : F 0 = 1) {A K R : ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hgauge : ∀ x, D.gauge (F x) ≤ A*‖x‖)
    (herror : ∀ x y, ‖x‖+‖y‖ ≤ R → D.metric.dist (F x*F y) (F (x+y)) ≤ K*‖x‖*‖y‖)
    (v : ℕ → E) (n : ℕ)
    (hR : 2*(∑ j ∈ Finset.range n, ‖v j‖) ≤ R)
    (hwindow : 2*A*(∑ j ∈ Finset.range n, ‖v j‖) ≤ 1/D.constant)
    (hquadratic : K*(∑ j ∈ Finset.range n, ‖v j‖)^2 ≤ 1/D.constant) :
    D.metric.dist (((List.range n).map (fun j => F (v j))).prod)
      (F (∑ j ∈ Finset.range n, v j)) ≤ K*2*(∑ j ∈ Finset.range n, ‖v j‖)^2 := by
  let S := ∑ j ∈ Finset.range n, ‖v j‖
  let s (k : ℕ) := ∑ j ∈ Finset.range k, v j
  let a (k : ℕ) := ((List.range k).map (fun j => F (v j))).prod
  let b (k : ℕ) := F (s k)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => norm_nonneg (v j))
  have hs (k : ℕ) (hk : k ≤ n) : ‖s k‖ ≤ S := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) (fun j _ _ => norm_nonneg (v j))
  have hv (k : ℕ) (hk : k < n) : ‖v k‖ ≤ S :=
    Finset.single_le_sum (fun j _ => norm_nonneg (v j)) (Finset.mem_range.mpr hk)
  have ha (k : ℕ) : (a k)⁻¹*a (k+1) = F (v k) := by
    dsimp [a]
    rw [List.prod_range_succ]
    group
  have he (k : ℕ) (hk : k < n) :
      D.metric.dist ((a k)⁻¹*a (k+1)) ((b k)⁻¹*b (k+1)) ≤ K*S*‖v k‖ := by
    rw [ha]
    have hl := D.left_invariant (b k) (F (v k)) ((b k)⁻¹*b (k+1))
    simp only [mul_inv_cancel_left] at hl
    rw [← hl]
    have hsk : s (k+1) = s k+v k := Finset.sum_range_succ v k
    dsimp only [b]
    rw [hsk]
    exact (herror _ _ (by have := hs k (by omega); have := hv k hk; dsimp [S] at *; linarith)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs k (by omega)) hK) (norm_nonneg _))
  have hstep (k : ℕ) (hk : k < n) :
      D.metric.dist ((a k)⁻¹*a (k+1)) ((b k)⁻¹*b (k+1)) ≤ 1/D.constant := by
    refine (he k hk).trans ((mul_le_mul_of_nonneg_left (hv k hk) (mul_nonneg hK hS)).trans ?_)
    nlinarith [hquadratic]
  have htail (k : ℕ) (hk : k ≤ n) : D.gauge ((b k)⁻¹*b n) ≤ 1/D.constant := by
    have h := D.gauge_mul_le ((b k)⁻¹) (b n)
    rw [D.gauge_inv] at h
    have h₁ := (hgauge (s k)).trans (mul_le_mul_of_nonneg_left (hs k hk) hA)
    have h₂ := (hgauge (s n)).trans (mul_le_mul_of_nonneg_left (hs n le_rfl) hA)
    exact (h.trans (add_le_add h₁ h₂)).trans (by dsimp [S] at *; linarith)
  have h := D.increment_comparison a b n (by simp [a]) (by simp [b,s,hF0]) hstep htail
  have hsum := Finset.sum_le_sum (fun k hk => he k (Finset.mem_range.mp hk))
  have hsum' : ∑ k ∈ Finset.range n, K*S*‖v k‖ = K*S*S := (Finset.mul_sum ..).symm
  rw [hsum'] at hsum
  exact h.trans ((mul_le_mul_of_nonneg_left hsum (by norm_num)).trans_eq (by ring))

end DirectedCycles.GleasonMetricData
