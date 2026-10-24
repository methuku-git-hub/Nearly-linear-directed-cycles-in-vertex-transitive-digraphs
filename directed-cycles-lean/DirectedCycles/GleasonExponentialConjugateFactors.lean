import DirectedCycles.GleasonConjugateProductApproximation
import DirectedCycles.GleasonCoordinateProductError
import DirectedCycles.GleasonCoordinateLowerBound

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- Each discrete adjoint exponential is the corresponding actual
conjugate factor in the power-product decomposition. -/
theorem coordinateExp_discrete_adjoint (y z : E) (n k : ℕ) :
    coordinateExp D e ((1/(n : ℝ)) •
      coordinateAdjoint D e (coordinateExp D e ((-((k : ℝ)/n)) • y)) z) =
    ((coordinateExp D e ((1/(n : ℝ)) • y))^k)⁻¹ *
      coordinateExp D e ((1/(n : ℝ)) • z) * (coordinateExp D e ((1/(n : ℝ)) • y))^k := by
  have hp : (coordinateExp D e ((1/(n : ℝ)) • y))^k = coordinateExp D e (((k : ℝ)/n) • y) := by
    rw [← coordinateExp_nat_smul,smul_smul,mul_one_div]
  rw [← map_smul,coordinateExp_adjoint,hp,neg_smul,coordinateExp_neg,inv_inv]

/-- Uniform vanishing error when the exact group difference is replaced
by the ordered exponential product of its discrete adjoint increments. -/
theorem coordinateExp_discrete_adjoint_error {r A : ℝ}
    (hp : ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r →
      (n : ℝ)*D.gauge h ≤ r → D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h)
    (hr : r ≤ 1/(8*D.constant)) (hA : 0 ≤ A)
    (hspeed : ∀ x : E, ∀ t : ℝ, D.gauge ((toOneParameter D (e.symm x)).eval t) ≤ A*‖x‖*|t|)
    (x y : E) (hsmall : A*(‖x‖+‖y‖) ≤ r) (n : ℕ) (hn : 0 < n) :
    D.metric.dist ((coordinateExp D e x)⁻¹*coordinateExp D e y)
      (((List.range n).map (fun k : ℕ => coordinateExp D e ((1/(n : ℝ)) •
        coordinateAdjoint D e (coordinateExp D e ((-((k : ℝ)/n)) • y)) (y-x)))).prod) ≤
      (16*D.constant*A^2*‖x‖*‖y‖)/(n : ℝ) := by
  have hC := D.constant_pos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  let t : ℝ := 1/(n : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; exact (div_le_one hnR).mpr hn1
  let g := coordinateExp D e (t • (-x))
  let h := coordinateExp D e (t • y)
  let u := coordinateExp D e (t • (y-x))
  have hgn : g^n = (coordinateExp D e x)⁻¹ := by
    dsimp [g]
    rw [← coordinateExp_nat_smul,smul_smul,show (n : ℝ)*t=1 by dsimp [t]; field_simp,one_smul,coordinateExp_neg]
  have hhn : h^n = coordinateExp D e y := by
    dsimp [h]
    rw [← coordinateExp_nat_smul,smul_smul,show (n : ℝ)*t=1 by dsimp [t]; field_simp,one_smul]
  have hgauge : D.gauge g ≤ A*t*‖x‖ := by
    simpa only [g,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht,norm_neg,mul_left_comm,mul_assoc] using
      coordinateExp_gauge_bound D e hspeed (t • (-x))
  have hhgauge : D.gauge h ≤ A*t*‖y‖ := by
    simpa only [h,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht,mul_left_comm,mul_assoc] using
      coordinateExp_gauge_bound D e hspeed (t • y)
  have hsum : 0 ≤ A*(‖x‖+‖y‖) := by positivity
  have htotal := hsmall.trans hr
  have hwindow : 2*(n : ℝ)*(D.gauge g+D.gauge h) ≤ 1/D.constant := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hgauge hhgauge) (show 0 ≤ 2*(n : ℝ) by positivity)
    have he : 2*(n : ℝ)*(A*t*‖x‖+A*t*‖y‖) = 2*A*(‖x‖+‖y‖) := by dsimp [t]; field_simp
    rw [he] at hh
    have hbound : 2*(1/(8*D.constant)) ≤ 1/D.constant := by field_simp; norm_num
    exact hh.trans (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left htotal (show (0 : ℝ) ≤ 2 by norm_num)).trans hbound)
  have hbase : D.metric.dist (g*h) u ≤ 4*D.constant*A^2*t^2*‖x‖*‖y‖ := by
    have hs : A*(‖t • (-x)‖+‖t • y‖) ≤ r := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht,norm_neg]
      have hh := mul_le_mul_of_nonneg_right ht1 hsum
      nlinarith
    have hh := coordinateExp_add_error D e hp hr hA hspeed (t • (-x)) (t • y) hs
    have he : t • (-x)+t • y = t • (y-x) := by module
    rw [he] at hh
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht,norm_neg] at hh
    exact hh.trans_eq (by ring)
  have herr : 2*D.metric.dist (g*h) u ≤ 1/D.constant := by
    have hx : A*‖x‖ ≤ 1/(8*D.constant) := (show A*‖x‖ ≤ A*(‖x‖+‖y‖) by nlinarith [norm_nonneg y]).trans htotal
    have hy : A*‖y‖ ≤ 1/(8*D.constant) := (show A*‖y‖ ≤ A*(‖x‖+‖y‖) by nlinarith [norm_nonneg x]).trans htotal
    have hprod := mul_le_mul hx hy (by positivity : 0 ≤ A*‖y‖) (by positivity : 0 ≤ 1/(8*D.constant))
    have hprod' := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 8*D.constant by positivity)
    have he : 8*D.constant*((1/(8*D.constant))*(1/(8*D.constant))) = 1/(8*D.constant) := by field_simp
    rw [he] at hprod'
    have htb : t^2 ≤ 1 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left htb (show 0 ≤ 8*D.constant*A^2*‖x‖*‖y‖ by positivity)
    have hfinal : 1/(8*D.constant) ≤ 1/D.constant := by apply div_le_div_of_nonneg_left (by norm_num) hC; linarith
    nlinarith [hfinal]
  have hc := D.power_product_conjugate_approximation g h u n hwindow herr
  rw [hgn,hhn] at hc
  have hlist : (List.range n).map (fun k : ℕ => (h^k)⁻¹*u*h^k) =
      (List.range n).map (fun k : ℕ => coordinateExp D e ((1/(n : ℝ)) •
        coordinateAdjoint D e (coordinateExp D e ((-((k : ℝ)/n)) • y)) (y-x))) := by
    apply List.map_congr_left
    intro k _
    exact (coordinateExp_discrete_adjoint D e y (y-x) n k).symm
  rw [hlist] at hc
  exact hc.trans ((mul_le_mul_of_nonneg_left hbase (show 0 ≤ 4*(n : ℝ) by positivity)).trans_eq (by dsimp [t]; field_simp; ring))

end DirectedCycles.GleasonLieAlgebra
