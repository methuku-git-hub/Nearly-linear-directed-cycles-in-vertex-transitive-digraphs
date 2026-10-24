import DirectedCycles.GleasonOneParameter
import DirectedCycles.GleasonPowerDistance

set_option autoImplicit false
namespace DirectedCycles
namespace OneParameter
variable {G : Type*} [Group G] [TopologicalSpace G]
/-- The actual finite product used in the Trotter construction. -/
noncomputable def productApprox (φ ψ : OneParameter G) (t : ℝ) (n : ℕ) : G :=
  (φ.eval (t/(n : ℝ))*ψ.eval (t/(n : ℝ)))^n
end OneParameter
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- Refining a power product only creates a quadratic error, amplified
linearly by the outer power. -/
theorem power_product_refinement {r : ℝ}
    (hpow : ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r →
      (n : ℝ)*D.gauge h ≤ r → D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h)
    (hr : r ≤ 1/(8*D.constant)) (g h : G) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hsmall : (n : ℝ)*(m : ℝ)*(D.gauge g+D.gauge h) ≤ r) :
    D.metric.dist ((g^m*h^m)^n) ((g*h)^(n*m)) ≤
      4*D.constant*(n : ℝ)*(m : ℝ)^2*D.gauge g*D.gauge h := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hg0 := D.gauge_nonneg g
  have hh0 := D.gauge_nonneg h
  have hbase : (m : ℝ)*(D.gauge g+D.gauge h) ≤ 1/(8*D.constant) := by
    have hnn := mul_le_mul_of_nonneg_right hn1 (mul_nonneg hm0 (add_nonneg hg0 hh0))
    nlinarith [hsmall.trans hr]
  have hA : (n : ℝ)*D.gauge (g^m*h^m) ≤ r := by
    have hmul := D.gauge_mul_le (g^m) (h^m)
    have h' : D.gauge (g^m*h^m) ≤ (m : ℝ)*(D.gauge g+D.gauge h) := by
      nlinarith [D.gauge_pow_le g m,D.gauge_pow_le h m]
    exact (mul_le_mul_of_nonneg_left h' (Nat.cast_nonneg n)).trans (by nlinarith [hsmall])
  have hB : (n : ℝ)*D.gauge ((g*h)^m) ≤ r := by
    have h' := (D.gauge_pow_le (g*h) m).trans (mul_le_mul_of_nonneg_left (D.gauge_mul_le g h) hm0)
    exact (mul_le_mul_of_nonneg_left h' (Nat.cast_nonneg n)).trans (by nlinarith [hsmall])
  have hp := hpow _ _ n hn hA hB
  rw [← pow_mul,Nat.mul_comm m n] at hp
  have hmprod := D.power_product_distance g h m hm hbase
  have hh := mul_le_mul_of_nonneg_left hmprod (by positivity : 0 ≤ 2*(n : ℝ))
  exact hp.trans (hh.trans_eq (by ring))

/-- Product approximations stay in a fixed small ball whenever the
summed parameter speeds are small. -/
theorem productApprox_gauge (φ ψ : OneParameter G) {L₁ L₂ : ℝ}
    (hφ : ∀ t : ℝ, D.gauge (φ.eval t) ≤ L₁*|t|)
    (hψ : ∀ t : ℝ, D.gauge (ψ.eval t) ≤ L₂*|t|)
    (t : ℝ) (n : ℕ) (hn : 0 < n) :
    D.gauge (φ.productApprox ψ t n) ≤ (L₁+L₂)*|t| := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := D.gauge_pow_le (φ.eval (t/(n : ℝ))*ψ.eval (t/(n : ℝ))) n
  have hsum : D.gauge (φ.eval (t/(n : ℝ))*ψ.eval (t/(n : ℝ))) ≤
      (L₁+L₂)*|t/(n : ℝ)| := by
    nlinarith [D.gauge_mul_le (φ.eval (t/(n : ℝ))) (ψ.eval (t/(n : ℝ))),hφ (t/(n : ℝ)),hψ (t/(n : ℝ))]
  apply h.trans
  calc
    (n : ℝ)*D.gauge (φ.eval (t/(n : ℝ))*ψ.eval (t/(n : ℝ))) ≤
        (n : ℝ)*((L₁+L₂)*|t/(n : ℝ)|) := mul_le_mul_of_nonneg_left hsum hnR.le
    _ = (L₁+L₂)*|t| := by rw [abs_div,abs_of_pos hnR]; field_simp

/-- The refinement error is bounded by a constant divided by the original
subdivision number, uniformly in the further refinement. -/
theorem productApprox_refinement {r : ℝ}
    (hpow : ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r →
      (n : ℝ)*D.gauge h ≤ r → D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h)
    (hr : r ≤ 1/(8*D.constant))
    (φ ψ : OneParameter G) {L₁ L₂ : ℝ} (hL₁ : 0 ≤ L₁)
    (hφ : ∀ t : ℝ, D.gauge (φ.eval t) ≤ L₁*|t|)
    (hψ : ∀ t : ℝ, D.gauge (ψ.eval t) ≤ L₂*|t|)
    (t : ℝ) (ht : (L₁+L₂)*|t| ≤ r) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    D.metric.dist (φ.productApprox ψ t n) (φ.productApprox ψ t (n*m)) ≤
      (4*D.constant*L₁*L₂*|t|^2)/(n : ℝ) := by
  have hC := D.constant_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let a : ℝ := t/((n : ℝ)*(m : ℝ))
  have ha : |a| = |t|/((n : ℝ)*(m : ℝ)) := by simp only [a,abs_div,abs_mul,abs_of_pos hnR,abs_of_pos hmR]
  have hsmall : (n : ℝ)*(m : ℝ)*(D.gauge (φ.eval a)+D.gauge (ψ.eval a)) ≤ r := by
    calc
      _ ≤ (n : ℝ)*(m : ℝ)*((L₁+L₂)*|a|) := by
        apply mul_le_mul_of_nonneg_left (by nlinarith [hφ a,hψ a]) (by positivity)
      _ = (L₁+L₂)*|t| := by rw [ha]; field_simp
      _ ≤ r := ht
  have he := D.power_product_refinement hpow hr (φ.eval a) (ψ.eval a) n m hn hm hsmall
  have hma : (m : ℝ)*a = t/(n : ℝ) := by dsimp [a]; field_simp
  rw [← φ.eval_nat_mul,← ψ.eval_nat_mul,hma] at he
  change D.metric.dist (φ.productApprox ψ t n) ((φ.eval a*ψ.eval a)^(n*m)) ≤ _ at he
  have hprod := mul_le_mul (hφ a) (hψ a) (D.gauge_nonneg _) (mul_nonneg hL₁ (abs_nonneg a))
  have hb := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 4*D.constant*(n : ℝ)*(m : ℝ)^2 by positivity)
  have hid : 4*D.constant*(n : ℝ)*(m : ℝ)^2*(L₁*|a| *(L₂*|a|)) =
      (4*D.constant*L₁*L₂*|t|^2)/(n : ℝ) := by rw [ha]; field_simp
  have hout := he.trans (show
      4*D.constant*(n : ℝ)*(m : ℝ)^2*D.gauge (φ.eval a)*D.gauge (ψ.eval a) ≤
        (4*D.constant*L₁*L₂*|t|^2)/(n : ℝ) from by
      calc
        _ = 4*D.constant*(n : ℝ)*(m : ℝ)^2*(D.gauge (φ.eval a)*D.gauge (ψ.eval a)) := by ring
        _ ≤ 4*D.constant*(n : ℝ)*(m : ℝ)^2*(L₁*|a| * (L₂*|a|)) := hb
        _ = _ := hid)
  simpa only [a,OneParameter.productApprox,Nat.cast_mul] using hout
end GleasonMetricData
end DirectedCycles
