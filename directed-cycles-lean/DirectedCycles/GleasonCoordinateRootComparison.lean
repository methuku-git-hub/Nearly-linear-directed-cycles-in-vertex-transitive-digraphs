module

public import DirectedCycles.GleasonCoordinateProductError
public import DirectedCycles.GleasonCoordinateLowerBound

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- Comparing reciprocal roots removes the quadratic product error at a
rate of one over the subdivision. Both power inequalities are retained. -/
theorem coordinate_root_comparison {r A : ℝ}
    (hp : ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r → (n : ℝ)*D.gauge h ≤ r →
      (n : ℝ)/(2*D.constant)*D.metric.dist g h ≤ D.metric.dist (g^n) (h^n) ∧
      D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h)
    (hr : r ≤ 1/(8*D.constant)) (hA : 0 ≤ A)
    (hspeed : ∀ x : E, ∀ t : ℝ, D.gauge ((toOneParameter D (e.symm x)).eval t) ≤ A*‖x‖*|t|)
    (x y : E) (hsmall : A*(‖x‖+‖y‖) ≤ r) (n : ℕ) (hn : 0 < n) :
    (n : ℝ)*D.gauge (coordinateExp D e ((1/(n : ℝ)) • (y-x))) ≤
      2*D.constant*D.metric.dist (coordinateExp D e x) (coordinateExp D e y) + (4*D.constant*A^2*‖x‖*‖y‖)/(n : ℝ) ∧
    D.metric.dist (coordinateExp D e x) (coordinateExp D e y) ≤
      2*(n : ℝ)*D.gauge (coordinateExp D e ((1/(n : ℝ)) • (y-x))) + 2*(4*D.constant*A^2*‖x‖*‖y‖)/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hC := D.constant_pos
  let q : ℝ := 1/(n : ℝ)
  have hq : 0 < q := one_div_pos.mpr hnR
  have hq1 : q ≤ 1 := (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn1).trans_eq (by norm_num)
  have hnq : (n : ℝ)*q = 1 := by dsimp [q]; field_simp
  have hnorm (z : E) : ‖q • z‖ = q*‖z‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hq]
  have hroot (z : E) : (n : ℝ)*D.gauge (coordinateExp D e (q • z)) ≤ A*‖z‖ := by
    rw [coordinateExp_smul]
    have h := mul_le_mul_of_nonneg_left (hspeed z q) hnR.le
    rw [abs_of_pos hq] at h
    exact h.trans_eq (by calc
      (n : ℝ)*(A*‖z‖*q) = ((n : ℝ)*q)*(A*‖z‖) := by ring
      _ = A*‖z‖ := by rw [hnq,one_mul])
  have hsmallx : A*‖x‖ ≤ r := by nlinarith [mul_nonneg hA (norm_nonneg y)]
  have hsmally : A*‖y‖ ≤ r := by nlinarith [mul_nonneg hA (norm_nonneg x)]
  have hpow := hp (coordinateExp D e (q • x)) (coordinateExp D e (q • y)) n hn
    ((hroot x).trans hsmallx) ((hroot y).trans hsmally)
  have hpower (z : E) : (coordinateExp D e (q • z))^n = coordinateExp D e z := by
    rw [← coordinateExp_nat_smul,smul_smul,hnq,one_smul]
  rw [hpower,hpower] at hpow
  have hsmallq : A*(‖q • x‖+‖q • y‖) ≤ r := by
    rw [hnorm,hnorm]
    have h := mul_le_mul_of_nonneg_right hq1 (mul_nonneg hA (add_nonneg (norm_nonneg x) (norm_nonneg y)))
    nlinarith
  have herr := coordinate_difference_gauge_error D e (fun g h n hn hg hh => (hp g h n hn hg hh).2)
    hr hA hspeed (q • x) (q • y) hsmallq
  rw [← smul_sub,hnorm,hnorm] at herr
  have herror : (n : ℝ)*(4*D.constant*A^2*(q*‖x‖)*(q*‖y‖)) =
      (4*D.constant*A^2*‖x‖*‖y‖)/(n : ℝ) := by dsimp [q]; field_simp
  have h₁ := mul_le_mul_of_nonneg_left herr.1 hnR.le
  have h₂ := mul_le_mul_of_nonneg_left herr.2 hnR.le
  rw [mul_add,herror] at h₁ h₂
  have hp₁ := mul_le_mul_of_nonneg_left hpow.1 (show 0 ≤ 2*D.constant by positivity)
  have hcanc : 2*D.constant*((n : ℝ)/(2*D.constant)*D.metric.dist (coordinateExp D e (q • x)) (coordinateExp D e (q • y))) =
      (n : ℝ)*D.metric.dist (coordinateExp D e (q • x)) (coordinateExp D e (q • y)) := by field_simp
  rw [hcanc] at hp₁
  constructor
  · exact h₁.trans (add_le_add_left hp₁ _)
  · dsimp only [q] at h₂ hpow
    apply hpow.2.trans
    have htwo := mul_le_mul_of_nonneg_left h₂ (by norm_num : (0 : ℝ) ≤ 2)
    convert htwo using 1 <;> ring

end DirectedCycles.GleasonLieAlgebra
