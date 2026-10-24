import DirectedCycles.GleasonPowerProduct

set_option autoImplicit false
namespace DirectedCycles
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- At a sufficiently small scale, power maps expand distances linearly.
The quantitative radius conditions are supplied by the next theorem. -/
theorem power_distance_of_radius {r : ℝ}
    (hr3 : 3*r ≤ 1/(8*D.constant)) (hr2 : 2*r ≤ 1/D.constant)
    (hrlower : 2*D.constant*r ≤ 1/(2*D.constant)) (hrupper : 2*D.constant*r ≤ 1)
    (g h : G) (n : ℕ) (hn : 0 < n)
    (hg : (n : ℝ)*D.gauge g ≤ r) (hh : (n : ℝ)*D.gauge h ≤ r) :
    (n : ℝ)/(2*D.constant)*D.metric.dist g h ≤ D.metric.dist (g^n) (h^n) ∧
      D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h := by
  have hC := D.constant_pos
  let k := h⁻¹*g
  have hk : h*k = g := by simp [k]
  have hknorm : D.gauge k = D.metric.dist g h := by
    rw [D.metric.dist_comm,D.dist_eq_gauge]
  have hk0 := D.gauge_nonneg k
  have hnk : (n : ℝ)*D.gauge k ≤ 2*r := by
    have ht : D.gauge k ≤ D.gauge h+D.gauge g := by
      simpa only [k,D.gauge_inv] using D.gauge_mul_le h⁻¹ g
    have ht' := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n)
    nlinarith
  have hmergeSmall : (n : ℝ)*(D.gauge h+D.gauge k) ≤ 1/(8*D.constant) := by
    nlinarith
  have hm := D.power_product_distance h k n hn hmergeSmall
  rw [hk] at hm
  have he : D.metric.dist (h^n*k^n) (h^n) = D.gauge (k^n) := by
    have hl := D.left_invariant (h^n) (k^n) 1
    simpa only [mul_one,gauge,D.metric.dist_comm] using hl
  have herrorLower : 2*D.constant*(n : ℝ)^2*D.gauge h*D.gauge k ≤
      (1/(2*D.constant))*(n : ℝ)*D.gauge k := by
    have hscale : 2*D.constant*((n : ℝ)*D.gauge h) ≤ 1/(2*D.constant) :=
      (mul_le_mul_of_nonneg_left hh (by positivity)).trans hrlower
    have ht := mul_le_mul_of_nonneg_right hscale (mul_nonneg (Nat.cast_nonneg n) hk0)
    nlinarith
  have herrorUpper : 2*D.constant*(n : ℝ)^2*D.gauge h*D.gauge k ≤
      (n : ℝ)*D.gauge k := by
    have hscale : 2*D.constant*((n : ℝ)*D.gauge h) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hh (by positivity)).trans hrupper
    have ht := mul_le_mul_of_nonneg_right hscale (mul_nonneg (Nat.cast_nonneg n) hk0)
    nlinarith
  have hesc := D.escape k n hn (hnk.trans hr2)
  change (n : ℝ)/D.constant*D.gauge k ≤ D.gauge (k^n) at hesc
  have hp := D.gauge_pow_le k n
  have htLower := D.metric.dist_triangle (h^n*k^n) (g^n) (h^n)
  rw [he] at htLower
  have htUpper := D.metric.dist_triangle (g^n) (h^n*k^n) (h^n)
  rw [he,D.metric.dist_comm (g^n) (h^n*k^n)] at htUpper
  constructor
  · rw [← hknorm]
    have hfrac : (n : ℝ)/D.constant = 2*((n : ℝ)/(2*D.constant)) := by ring
    rw [hfrac] at hesc
    have hlow : D.metric.dist (h^n*k^n) (g^n) ≤
        (n : ℝ)/(2*D.constant)*D.gauge k := by
      exact (hm.trans herrorLower).trans_eq (by ring)
    nlinarith
  · rw [← hknorm]
    have hupper := hm.trans herrorUpper
    nlinarith

/-- A single strictly positive radius works uniformly for every power
and every pair of group elements at the corresponding inverse scale. -/
theorem exists_power_distance_radius : ∃ r : ℝ, 0 < r ∧
    ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r → (n : ℝ)*D.gauge h ≤ r →
      (n : ℝ)/(2*D.constant)*D.metric.dist g h ≤ D.metric.dist (g^n) (h^n) ∧
        D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h := by
  let r := min (1/(24*D.constant)) (min (1/(4*D.constant^2)) (1/(2*D.constant)))
  have hC := D.constant_pos
  have hr : 0 < r := by dsimp [r]; positivity
  have hrA : r ≤ 1/(24*D.constant) := min_le_left _ _
  have hrB : r ≤ 1/(4*D.constant^2) := (min_le_right _ _).trans (min_le_left _ _)
  have hrC : r ≤ 1/(2*D.constant) := (min_le_right _ _).trans (min_le_right _ _)
  have hr3 : 3*r ≤ 1/(8*D.constant) := by
    have h := mul_le_mul_of_nonneg_left hrA (by norm_num : (0 : ℝ) ≤ 3)
    exact h.trans_eq (by ring)
  have hr2 : 2*r ≤ 1/D.constant := by
    have h := mul_le_mul_of_nonneg_left hrC (by norm_num : (0 : ℝ) ≤ 2)
    exact h.trans_eq (by ring)
  have hrlower : 2*D.constant*r ≤ 1/(2*D.constant) := by
    have h := mul_le_mul_of_nonneg_left hrB (show 0 ≤ 2*D.constant by positivity)
    apply h.trans_eq
    field_simp
    ring
  have hrupper : 2*D.constant*r ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hrC (show 0 ≤ 2*D.constant by positivity)
    simpa only [mul_one_div_cancel (by positivity : 2*D.constant ≠ 0)] using h
  exact ⟨r,hr,fun g h n hn hg hh => D.power_distance_of_radius hr3 hr2 hrlower hrupper g h n hn hg hh⟩
end GleasonMetricData
end DirectedCycles
