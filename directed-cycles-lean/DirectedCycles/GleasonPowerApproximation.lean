import DirectedCycles.GleasonTrotterControl

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- A quadratic error between two small curves vanishes after taking the
usual subdivision powers. This transfers actual limits between the curves. -/
theorem powerApprox_tendsto_transfer {r L K t : ℝ} (hL : 0 ≤ L)
    (hp : ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r →
      (n : ℝ)*D.gauge h ≤ r → D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h)
    (f g : ℝ → G)
    (hf : ∀ u : ℝ, L*|u| ≤ r → D.gauge (f u) ≤ L*|u|)
    (hg : ∀ u : ℝ, L*|u| ≤ r → D.gauge (g u) ≤ L*|u|)
    (he : ∀ u : ℝ, L*|u| ≤ r → D.metric.dist (f u) (g u) ≤ K*|u|^2)
    (ht : L*|t| ≤ r) {x : G}
    (hlim : Tendsto (fun n : ℕ => (f (t/(n : ℝ)))^n) atTop (𝓝 x)) :
    Tendsto (fun n : ℕ => (g (t/(n : ℝ)))^n) atTop (𝓝 x) := by
  let : MetricSpace G := D.compatibleMetric
  apply hlim.congr_dist
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg)) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (2*K*|t|^2))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnt : |t/(n : ℝ)| ≤ |t| := by
    rw [abs_div,abs_of_pos hnR]
    apply (div_le_iff₀ hnR).mpr
    nlinarith [abs_nonneg t]
  have hsmall : L*|t/(n : ℝ)| ≤ r := (mul_le_mul_of_nonneg_left hnt hL).trans ht
  have hid : (n : ℝ)*(L*|t/(n : ℝ)|) = L*|t| := by
    rw [abs_div,abs_of_pos hnR]
    field_simp
  have hfn : (n : ℝ)*D.gauge (f (t/(n : ℝ))) ≤ r :=
    (mul_le_mul_of_nonneg_left (hf _ hsmall) hnR.le).trans (hid.le.trans ht)
  have hgn : (n : ℝ)*D.gauge (g (t/(n : ℝ))) ≤ r :=
    (mul_le_mul_of_nonneg_left (hg _ hsmall) hnR.le).trans (hid.le.trans ht)
  have hh := hp (f (t/(n : ℝ))) (g (t/(n : ℝ))) n (by omega) hfn hgn
  have hb := mul_le_mul_of_nonneg_left (he _ hsmall) (show 0 ≤ 2*(n : ℝ) by positivity)
  apply hh.trans (hb.trans_eq ?_)
  rw [abs_div,abs_of_pos hnR]
  field_simp
end GleasonMetricData
end DirectedCycles
