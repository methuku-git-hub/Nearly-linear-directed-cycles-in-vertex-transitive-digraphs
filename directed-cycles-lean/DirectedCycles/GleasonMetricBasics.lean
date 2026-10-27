module

public import DirectedCycles.NSSGleasonMetric

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- The identity distance in the actual constructed Gleason metric. -/
def gauge (g : G) : ℝ := D.metric.dist 1 g

theorem gauge_nonneg (g : G) : 0 ≤ D.gauge g := by
  let : MetricSpace G := D.metric
  exact dist_nonneg

theorem gauge_one : D.gauge (1 : G) = 0 := D.metric.dist_self _

theorem gauge_eq_zero_iff (g : G) : D.gauge g = 0 ↔ g = 1 := by
  constructor
  · intro h
    exact (D.metric.eq_of_dist_eq_zero h).symm
  · rintro rfl
    exact D.gauge_one

theorem dist_eq_gauge (x y : G) : D.metric.dist x y = D.gauge (x⁻¹*y) := by
  have h := D.left_invariant x⁻¹ x y
  simpa only [gauge,inv_mul_cancel] using h.symm

theorem gauge_inv (g : G) : D.gauge g⁻¹ = D.gauge g := by
  have h := D.left_invariant g⁻¹ g 1
  change D.metric.dist 1 g⁻¹ = D.metric.dist 1 g
  simpa only [inv_mul_cancel,mul_one] using h.trans (D.metric.dist_comm g 1)

theorem gauge_mul_le (g h : G) : D.gauge (g*h) ≤ D.gauge g+D.gauge h := by
  have ht := D.metric.dist_triangle 1 g (g*h)
  have he := D.left_invariant g 1 h
  simp only [mul_one] at he
  rw [he] at ht
  exact ht

theorem gauge_pow_le (g : G) (n : ℕ) : D.gauge (g^n) ≤ (n : ℝ)*D.gauge g := by
  induction n with
  | zero => simp only [pow_zero,D.gauge_one,Nat.cast_zero,zero_mul,le_refl]
  | succ n ih =>
      rw [pow_succ]
      exact (D.gauge_mul_le _ _).trans ((add_le_add ih le_rfl).trans_eq (by push_cast; ring))

theorem gauge_zpow_le (g : G) (n : ℤ) : D.gauge (g^n) ≤ (n.natAbs : ℝ)*D.gauge g := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast,zpow_natCast,Int.natAbs_natCast] using D.gauge_pow_le g n
  | negSucc n => simpa only [zpow_negSucc,D.gauge_inv,Int.natAbs_negSucc] using D.gauge_pow_le g (n+1)

theorem dist_le_gauges (x y : G) : D.metric.dist x y ≤ D.gauge x+D.gauge y := by
  rw [D.dist_eq_gauge]
  simpa only [D.gauge_inv] using D.gauge_mul_le x⁻¹ y

/-- The commutator estimate gives local quantitative control of conjugation. -/
theorem gauge_conjugate_le (g h : G) (hg : D.gauge g ≤ 1/D.constant)
    (hh : D.gauge h ≤ 1/D.constant) :
    D.gauge (h⁻¹*g*h) ≤ (1+D.constant*D.gauge h)*D.gauge g := by
  have he : h⁻¹*g*h = g*(g⁻¹*h⁻¹*g*h) := by group
  rw [he]
  have hc := D.commutator g h hg hh
  exact (D.gauge_mul_le _ _).trans ((add_le_add le_rfl hc).trans_eq (by dsimp [gauge]; ring))

/-- Right translation is uniformly Lipschitz on sufficiently small windows. -/
theorem dist_mul_right_le_two (x y z : G)
    (hxy : D.metric.dist x y ≤ 1/D.constant) (hz : D.gauge z ≤ 1/D.constant) :
    D.metric.dist (x*z) (y*z) ≤ 2*D.metric.dist x y := by
  rw [D.dist_eq_gauge] at hxy
  rw [D.dist_eq_gauge (x*z) (y*z),D.dist_eq_gauge x y]
  have he : (x*z)⁻¹*(y*z) = z⁻¹*(x⁻¹*y)*z := by group
  rw [he]
  have h := D.gauge_conjugate_le (x⁻¹*y) z hxy hz
  have hc : D.constant*D.gauge z ≤ 1 := by
    have hc' := (le_div_iff₀ D.constant_pos).mp hz
    nlinarith
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (D.gauge_nonneg _))

/-- Exchanging two small factors has quadratic error. -/
theorem dist_mul_swap_le (g h : G) (hg : D.gauge g ≤ 1/D.constant)
    (hh : D.gauge h ≤ 1/D.constant) :
    D.metric.dist (g*h) (h*g) ≤ D.constant*D.gauge g*D.gauge h := by
  rw [D.dist_eq_gauge]
  have he : (g*h)⁻¹*(h*g) = h⁻¹*g⁻¹*h*g := by group
  rw [he]
  exact (D.commutator h g hh hg).trans_eq (by dsimp [gauge]; ring)
end GleasonMetricData
end DirectedCycles
