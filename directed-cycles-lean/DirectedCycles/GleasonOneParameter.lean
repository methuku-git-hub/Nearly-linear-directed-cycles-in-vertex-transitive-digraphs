import DirectedCycles.GleasonPowerPrefix
import DirectedCycles.GleasonMetricTopology
import Mathlib.Topology.Algebra.Group.CompactOpen
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles

/-- Actual continuous one-parameter homomorphisms, with their compact-open topology. -/
abbrev OneParameter (G : Type*) [Group G] [TopologicalSpace G] :=
  ContinuousMonoidHom (Multiplicative ℝ) G

namespace OneParameter
variable {G : Type*} [Group G] [TopologicalSpace G]

def eval (φ : OneParameter G) (t : ℝ) : G := φ (Multiplicative.ofAdd t)

@[simp] theorem eval_zero (φ : OneParameter G) : φ.eval 0 = 1 := map_one φ

theorem eval_add (φ : OneParameter G) (s t : ℝ) :
    φ.eval (s+t) = φ.eval s * φ.eval t := map_mul φ _ _

theorem eval_neg (φ : OneParameter G) (t : ℝ) :
    φ.eval (-t) = (φ.eval t)⁻¹ := map_inv φ _

theorem eval_sub (φ : OneParameter G) (s t : ℝ) :
    φ.eval (s-t) = (φ.eval t)⁻¹ * φ.eval s := by
  rw [sub_eq_neg_add, eval_add, eval_neg]

theorem eval_nat_mul (φ : OneParameter G) (n : ℕ) (t : ℝ) :
    φ.eval ((n : ℝ)*t) = (φ.eval t)^n := by
  change φ (Multiplicative.ofAdd ((n : ℝ)*t)) = _
  rw [← nsmul_eq_mul, ofAdd_nsmul, map_pow]
  rfl

theorem continuous_eval (φ : OneParameter G) : Continuous φ.eval := φ.continuous
end OneParameter

namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- Uniform smallness on a parameter interval gives a quantitative linear
bound, by applying the escape estimate to a long segment of integer powers. -/
theorem oneParameter_gauge_local (φ : OneParameter G) {T R : ℝ}
    (hT : 0 < T) (hR : 0 ≤ R) (hscale : (D.constant+1)*R ≤ 1/D.constant)
    (hφ : ∀ t : ℝ, |t| ≤ T → D.gauge (φ.eval t) ≤ R)
    (t : ℝ) (ht : |t| ≤ T) :
    D.gauge (φ.eval t) ≤ (2*D.constant*R/T)*|t| := by
  by_cases ht0 : t = 0
  · subst t
    simp [D.gauge_one]
  · have htpos : 0 < |t| := abs_pos.mpr ht0
    let N : ℕ := ⌊T/|t|⌋₊
    have hN : 1 ≤ N := (Nat.one_le_floor_iff _).mpr ((le_div_iff₀ htpos).mpr (by simpa using ht))
    have hNa : (N : ℝ)*|t| ≤ T := (le_div_iff₀ htpos).mp (Nat.floor_le (div_nonneg hT.le htpos.le))
    have hNb : T < ((N : ℝ)+1)*|t| := (div_lt_iff₀ htpos).mp (Nat.lt_floor_add_one (T/|t|))
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hp : ∀ k ≤ N, D.gauge ((φ.eval t)^k) ≤ R := by
      intro k hk
      rw [← φ.eval_nat_mul]
      apply hφ
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) htpos.le).trans hNa
    have he := D.gauge_linear_of_power_prefix (φ.eval t) N hR hscale hp
    have hν := D.gauge_nonneg (φ.eval t)
    have hNbig : T ≤ 2*(N : ℝ)*|t| := by nlinarith
    have hb : D.gauge (φ.eval t) ≤ (2*D.constant*R*|t|)/T := by
      apply (le_div_iff₀ hT).mpr
      nlinarith [mul_le_mul_of_nonneg_right he htpos.le,
        mul_le_mul_of_nonneg_right hNbig hν]
    convert hb using 1; ring

/-- A linear estimate near zero for a one-parameter subgroup extends to all
real parameters by division into finitely many equal increments. -/
theorem oneParameter_gauge_global_of_local (φ : OneParameter G) {T L : ℝ}
    (hT : 0 < T) (hlocal : ∀ t : ℝ, |t| ≤ T → D.gauge (φ.eval t) ≤ L*|t|)
    (t : ℝ) : D.gauge (φ.eval t) ≤ L*|t| := by
  obtain ⟨m,hm⟩ := exists_nat_gt (|t|/T)
  have hmpos : (0 : ℝ) < m := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hT.le) hm
  have hmsmall : |t/(m : ℝ)| ≤ T := by
    rw [abs_div,abs_of_pos hmpos]
    exact (div_le_iff₀ hmpos).mpr (le_of_lt ((div_lt_iff₀ hT).mp hm) |>.trans_eq (mul_comm _ _))
  have he := D.gauge_pow_le (φ.eval (t/(m : ℝ))) m
  rw [← φ.eval_nat_mul, mul_div_cancel₀ t (ne_of_gt hmpos)] at he
  have h := mul_le_mul_of_nonneg_left (hlocal _ hmsmall) hmpos.le
  calc
    D.gauge (φ.eval t) ≤ (m : ℝ)*(L*|t/(m : ℝ)|) := he.trans h
    _ = L*|t| := by rw [abs_div,abs_of_pos hmpos]; field_simp

/-- One common smallness interval yields one common global Lipschitz bound. -/
theorem oneParameter_gauge_bound (φ : OneParameter G) {T R : ℝ}
    (hT : 0 < T) (hR : 0 ≤ R) (hscale : (D.constant+1)*R ≤ 1/D.constant)
    (hφ : ∀ t : ℝ, |t| ≤ T → D.gauge (φ.eval t) ≤ R) (t : ℝ) :
    D.gauge (φ.eval t) ≤ (2*D.constant*R/T)*|t| :=
  D.oneParameter_gauge_global_of_local φ hT
    (fun t ht => D.oneParameter_gauge_local φ hT hR hscale hφ t ht) t

 theorem oneParameter_dist_bound (φ : OneParameter G) {T R : ℝ}
    (hT : 0 < T) (hR : 0 ≤ R) (hscale : (D.constant+1)*R ≤ 1/D.constant)
    (hφ : ∀ t : ℝ, |t| ≤ T → D.gauge (φ.eval t) ≤ R) (s t : ℝ) :
    D.metric.dist (φ.eval s) (φ.eval t) ≤ (2*D.constant*R/T)*|t-s| := by
  rw [D.dist_eq_gauge, ← φ.eval_sub]
  exact D.oneParameter_gauge_bound φ hT hR hscale hφ (t-s)
end GleasonMetricData
end DirectedCycles
