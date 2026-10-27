module

public import DirectedCycles.GleasonTrotterExistence

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- A constructed positive radius simultaneously supports both estimates
used in the Trotter construction. -/
theorem exists_trotter_radius : ∃ r : ℝ, 0 < r ∧ r ≤ 1/(8*D.constant) ∧
    ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r →
      (n : ℝ)*D.gauge h ≤ r → D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h := by
  obtain ⟨r₀,hr₀,hp₀⟩ := D.exists_power_distance_radius
  have hC := D.constant_pos
  refine ⟨min r₀ (1/(8*D.constant)),lt_min hr₀ (by positivity),min_le_right _ _,?_⟩
  intro g h n hn hg hh
  exact (hp₀ g h n hn (hg.trans (min_le_left _ _)) (hh.trans (min_le_left _ _))).2

variable [IsTopologicalGroup G] [LocallyCompactSpace G]
    {r : ℝ}
    (hpow : ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r →
      (n : ℝ)*D.gauge h ≤ r → D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h)
    (hr : r ≤ 1/(8*D.constant))
    (φ ψ : OneParameter G) {L₁ L₂ : ℝ} (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hφ : ∀ t : ℝ, D.gauge (φ.eval t) ≤ L₁*|t|)
    (hψ : ∀ t : ℝ, D.gauge (ψ.eval t) ≤ L₂*|t|)
include hpow hr hL₁ hL₂ hφ hψ

/-- Local uniqueness and integer rescaling identify the global sum with
the product limit throughout the entire quantitative small interval. -/
theorem productLimit_eq_of_isTrotterSum {ζ : OneParameter G}
    (hζ : OneParameter.IsTrotterSum φ ψ ζ) (t : ℝ) (ht : (L₁+L₂)*|t| ≤ r) :
    φ.productLimit ψ t = ζ.eval t := by
  let : MetricSpace G := D.compatibleMetric
  obtain ⟨δ,hδ,hζ⟩ := hζ
  obtain ⟨k,hk⟩ := exists_nat_gt (max (|t|/δ) 1)
  have hk1 : (1 : ℝ) < k := lt_of_le_of_lt (le_max_right _ _) hk
  have hkR : (0 : ℝ) < k := lt_trans zero_lt_one hk1
  have hkpos : 0 < k := by exact_mod_cast hkR
  let x := t/(k : ℝ)
  have hxδ : |x| ≤ δ := by
    rw [show |x| = |t|/(k : ℝ) by simp only [x,abs_div,abs_of_pos hkR]]
    apply (div_le_iff₀ hkR).mpr
    nlinarith [(div_lt_iff₀ hδ).mp (lt_of_le_of_lt (le_max_left _ _) hk)]
  have hxt : |x| ≤ |t| := by
    rw [show |x| = |t|/(k : ℝ) by simp only [x,abs_div,abs_of_pos hkR]]
    apply (div_le_iff₀ hkR).mpr
    nlinarith [abs_nonneg t]
  have hx : (L₁+L₂)*|x| ≤ r :=
    (mul_le_mul_of_nonneg_left hxt (add_nonneg hL₁ hL₂)).trans ht
  have hagree : ζ.eval x = φ.productLimit ψ x :=
    tendsto_nhds_unique (hζ x hxδ) (D.productLimit_tendsto hpow hr φ ψ hL₁ hφ hψ x hx)
  have hmul : (k : ℝ)*x = t := mul_div_cancel₀ _ (ne_of_gt hkR)
  have he := D.productLimit_nat_mul hpow hr φ ψ hL₁ hφ hψ x k hkpos hx (by simpa only [hmul] using ht)
  rw [hmul,← hagree,← ζ.eval_nat_mul,hmul] at he
  exact he

theorem trotterSum_distance (t : ℝ) (ht : (L₁+L₂)*|t| ≤ r) (n : ℕ) (hn : 0 < n) :
    D.metric.dist (φ.productApprox ψ t n) ((D.trotterSum φ ψ).eval t) ≤
      (4*D.constant*L₁*L₂*|t|^2)/(n : ℝ) := by
  rw [← D.productLimit_eq_of_isTrotterSum hpow hr φ ψ hL₁ hL₂ hφ hψ (D.trotterSum_spec φ ψ) t ht]
  exact D.productLimit_distance hpow hr φ ψ hL₁ hφ hψ t ht n hn

theorem trotterSum_gauge_local (t : ℝ) (ht : (L₁+L₂)*|t| ≤ r) :
    D.gauge ((D.trotterSum φ ψ).eval t) ≤ (L₁+L₂)*|t| := by
  rw [← D.productLimit_eq_of_isTrotterSum hpow hr φ ψ hL₁ hL₂ hφ hψ (D.trotterSum_spec φ ψ) t ht]
  exact D.productLimit_gauge hpow hr φ ψ hL₁ hφ hψ t ht

omit hpow hr in
/-- The global speed of the actual sum is bounded by the sum of the two
input speed bounds. -/
theorem trotterSum_gauge (t : ℝ) :
    D.gauge ((D.trotterSum φ ψ).eval t) ≤ (L₁+L₂)*|t| := by
  obtain ⟨r,hrpos,hr,hp⟩ := D.exists_trotter_radius
  have hL : 0 < L₁+L₂+1 := by linarith
  let T := r/(L₁+L₂+1)
  have hT : 0 < T := div_pos hrpos hL
  have hscale : (L₁+L₂)*T ≤ r := by
    have hid : (L₁+L₂+1)*T = r := mul_div_cancel₀ _ (ne_of_gt hL)
    nlinarith
  apply D.oneParameter_gauge_global_of_local (D.trotterSum φ ψ) hT ?_ t
  intro s hs
  exact D.trotterSum_gauge_local hp hr φ ψ hL₁ hL₂ hφ hψ s
    ((mul_le_mul_of_nonneg_left hs (add_nonneg hL₁ hL₂)).trans hscale)
end GleasonMetricData
end DirectedCycles
