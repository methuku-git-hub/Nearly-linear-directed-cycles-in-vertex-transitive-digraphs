import DirectedCycles.GleasonExponentialSmallSpeed

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace GleasonLieAlgebra
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- A normalised power limit supplies a vector perturbation strictly closer
than a nearest point. Every scale, approximation bound and neighbourhood
condition is explicit in this contradiction lemma. -/
theorem no_nearest_normalized_power_family {ι : Type*} {l : Filter ι} [l.NeBot]
    {K : Set (GleasonLieAlgebra D)} (hK : K ∈ 𝓝 0) {r R : ℝ}
    (hrpos : 0 < r) (hRpos : 0 < R) (hRr : R ≤ r) (hr : r ≤ 1/(8*D.constant))
    (hp : ∀ a b : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge a ≤ r → (n : ℝ)*D.gauge b ≤ r →
      (n : ℝ)/(2*D.constant)*D.metric.dist a b ≤ D.metric.dist (a^n) (b^n) ∧
      D.metric.dist (a^n) (b^n) ≤ 2*(n : ℝ)*D.metric.dist a b)
    (g k : ι → G) (x : ι → GleasonLieAlgebra D) (N : ι → ℕ)
    (hx : Tendsto x l (𝓝 0)) (hN : Tendsto N l atTop)
    (hlink : ∀ᶠ i in l, g i = exp D (x i)*k i)
    (hmin : ∀ᶠ i in l, ∀ y ∈ K, D.gauge (k i) ≤ D.metric.dist (g i) (exp D y))
    (hscale : ∀ᶠ i in l, 0 < N i ∧ R/2 ≤ (N i : ℝ)*D.gauge (k i) ∧ (N i : ℝ)*D.gauge (k i) ≤ R)
    (v : GleasonLieAlgebra D)
    (hv : ∀ t : ℝ, D.gauge ((toOneParameter D v).eval t) ≤ R*|t|)
    (hlimit : Tendsto (fun i => (k i)^(N i)) l (𝓝 (exp D v))) : False := by
  let : MetricSpace G := D.compatibleMetric
  have hC := D.constant_pos
  let ε := min (r/4) (1/(32*D.constant))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεr : ε ≤ r/4 := min_le_left _ _
  have hεC : 32*D.constant*ε ≤ 1 := by
    have h := (le_div_iff₀ (show 0 < 32*D.constant by positivity)).mp (min_le_right (r/4) (1/(32*D.constant)))
    nlinarith
  have hspeed := eventually_small_speed D hx hε
  have hcoeff : Tendsto (fun i => R/(N i : ℝ)) l (𝓝 (0 : ℝ)) :=
    (tendsto_const_div_atTop_nhds_zero_nat R).comp hN
  have hcoeffsmall : ∀ᶠ i in l, R/(N i : ℝ) < r/2 := hcoeff.eventually (gt_mem_nhds (half_pos hrpos))
  have hscalar : Tendsto (fun i => 1/(N i : ℝ)) l (𝓝 (0 : ℝ)) :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hN
  have hperturb : Tendsto (fun i => x i+(1/(N i : ℝ)) • v) l (𝓝 0) := by
    simpa only [zero_smul,add_zero] using hx.add (hscalar.smul (tendsto_const_nhds (x := v)))
  have hmember : ∀ᶠ i in l, x i+(1/(N i : ℝ)) • v ∈ K := hperturb.eventually hK
  have hdlim : Tendsto (fun i => D.metric.dist ((k i)^(N i)) (exp D v)) l (𝓝 (0 : ℝ)) := by
    simpa only [dist_self] using hlimit.dist (tendsto_const_nhds (x := exp D v))
  have hclose : ∀ᶠ i in l, D.metric.dist ((k i)^(N i)) (exp D v) < R/(16*D.constant) :=
    hdlim.eventually (gt_mem_nhds (by positivity))
  have hbad : ∀ᶠ i in l, False := by
    filter_upwards [hspeed,hcoeffsmall,hmember,hclose,hlink,hmin,hscale] with i hxi hci hmem hcl hgi hmi hsi
    have hnR : (0 : ℝ) < N i := by exact_mod_cast hsi.1
    let w : GleasonLieAlgebra D := (1/(N i : ℝ)) • v
    have hw : ∀ t : ℝ, D.gauge ((toOneParameter D w).eval t) ≤ (R/(N i : ℝ))*|t| := by
      intro t
      change D.gauge ((toOneParameter D v).eval ((1/(N i : ℝ))*t)) ≤ _
      have h := hv ((1/(N i : ℝ))*t)
      rw [abs_mul,abs_of_pos (one_div_pos.mpr hnR)] at h
      exact h.trans_eq (by ring)
    have hsmall : ε+R/(N i : ℝ) ≤ r := by linarith
    have herror := exp_add_error D (fun a b n hn ha hb => (hp a b n hn ha hb).2) hr
      (x i) w hε.le (div_nonneg hRpos.le hnR.le) hxi hw hsmall
    have hnφ : (N i : ℝ)*D.gauge ((toOneParameter D v).eval (1/(N i : ℝ))) ≤ r := by
      have h := mul_le_mul_of_nonneg_left (hv (1/(N i : ℝ))) hnR.le
      have hid : (N i : ℝ)*(R*|1/(N i : ℝ)|) = R := by
        rw [abs_of_pos (one_div_pos.mpr hnR)]
        field_simp
      exact (h.trans_eq hid).trans hRr
    have hbase := (hp (k i) ((toOneParameter D v).eval (1/(N i : ℝ))) (N i) hsi.1 (hsi.2.2.trans hRr) hnφ).1
    have hmul : (N i : ℝ)*(1/(N i : ℝ)) = 1 := by field_simp
    rw [← OneParameter.eval_nat_mul,hmul] at hbase
    have hform : (N i : ℝ)/(2*D.constant)*D.metric.dist (k i) ((toOneParameter D v).eval (1/(N i : ℝ))) =
        ((N i : ℝ)*D.metric.dist (k i) ((toOneParameter D v).eval (1/(N i : ℝ))))/(2*D.constant) := by ring
    rw [hform] at hbase
    have hbase' := (div_le_iff₀ (show 0 < 2*D.constant by positivity)).mp hbase
    have hexpw : exp D w = (toOneParameter D v).eval (1/(N i : ℝ)) := exp_smul D _ v
    have ht := D.metric.dist_triangle (g i) (exp D (x i)*exp D w) (exp D (x i+w))
    rw [hgi,D.left_invariant,hexpw] at ht
    have hnear := hmi (x i+w) hmem
    rw [hgi] at hnear
    rw [hexpw] at herror
    have hbound : D.gauge (k i) ≤ D.metric.dist (k i) ((toOneParameter D v).eval (1/(N i : ℝ))) +
        4*D.constant*ε*(R/(N i : ℝ)) := by
      exact hnear.trans (ht.trans (add_le_add_right herror _))
    have hscaled := mul_le_mul_of_nonneg_left hbound hnR.le
    have hid : (N i : ℝ)*(4*D.constant*ε*(R/(N i : ℝ))) = 4*D.constant*ε*R := by field_simp
    rw [mul_add,hid] at hscaled
    have hcl' := (lt_div_iff₀ (show 0 < 16*D.constant by positivity)).mp hcl
    have hεCR := mul_le_mul_of_nonneg_right hεC hRpos.le
    change (N i : ℝ)*D.metric.dist (k i) ((toOneParameter D v).eval (1/(N i : ℝ))) ≤
      D.metric.dist ((k i)^(N i)) (exp D v)*(2*D.constant) at hbase'
    nlinarith [hsi.2.1]
  exact (hbad.exists).choose_spec
end GleasonLieAlgebra
end DirectedCycles
