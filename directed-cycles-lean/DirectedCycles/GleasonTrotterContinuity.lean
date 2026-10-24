import DirectedCycles.GleasonOneParameterNeighbourhood
import DirectedCycles.GleasonTrotterControl

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- The product approximations converge uniformly when both inputs range
through any family with a common speed bound and the parameter stays small. -/
theorem trotterSum_eval_continuousOn {r L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hp : ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r →
      (n : ℝ)*D.gauge h ≤ r → D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h)
    (hr : r ≤ 1/(8*D.constant)) (hscale : 2*L*T ≤ r)
    (N : Set (OneParameter G × OneParameter G))
    (hN : ∀ p ∈ N, ∀ t : ℝ, D.gauge (p.1.eval t) ≤ L*|t| ∧ D.gauge (p.2.eval t) ≤ L*|t|) :
    ContinuousOn (fun p : (OneParameter G × OneParameter G) × ℝ =>
      (D.trotterSum p.1.1 p.1.2).eval p.2) (N ×ˢ {t : ℝ | |t| ≤ T}) := by
  let : MetricSpace G := D.compatibleMetric
  have hC := D.constant_pos
  have hu : TendstoUniformlyOn
      (fun n (p : (OneParameter G × OneParameter G) × ℝ) => p.1.1.productApprox p.1.2 p.2 n)
      (fun p => (D.trotterSum p.1.1 p.1.2).eval p.2) atTop (N ×ˢ {t : ℝ | |t| ≤ T}) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    let K : ℝ := 4*D.constant*L*L*T^2
    have hev : ∀ᶠ n : ℕ in atTop, K/(n : ℝ) < ε :=
      (tendsto_const_div_atTop_nhds_zero_nat K).eventually (gt_mem_nhds hε)
    filter_upwards [hev,eventually_ge_atTop 1] with n hn hn1
    intro p hpmem
    have hsmall : (L+L)*|p.2| ≤ r := by nlinarith [hpmem.2,mul_le_mul_of_nonneg_left hpmem.2 hL]
    have hd := D.trotterSum_distance hp hr p.1.1 p.1.2 hL hL
      (fun t => (hN p.1 hpmem.1 t).1) (fun t => (hN p.1 hpmem.1 t).2) p.2 hsmall n (by omega)
    have hpt : |p.2| ≤ T := hpmem.2
    have ht2 : |p.2|^2 ≤ T^2 := by nlinarith [abs_nonneg p.2]
    have hK : 4*D.constant*L*L*|p.2|^2 ≤ K :=
      mul_le_mul_of_nonneg_left ht2 (by positivity)
    have hh := hd.trans (div_le_div_of_nonneg_right hK (Nat.cast_nonneg n))
    change D.metric.dist ((D.trotterSum p.1.1 p.1.2).eval p.2) (p.1.1.productApprox p.1.2 p.2 n) < ε
    rw [D.metric.dist_comm]
    exact hh.trans_lt hn
  apply hu.continuousOn
  exact (Filter.Eventually.of_forall (fun n => (OneParameter.continuous_productApprox (G := G) n).continuousOn)).frequently

/-- Evaluation of the constructed sum is jointly continuous in both
one-parameter inputs and the real parameter. Finite subdivision transports
the uniformly controlled small interval to every real parameter. -/
theorem continuous_trotterSum_eval :
    Continuous (fun p : (OneParameter G × OneParameter G) × ℝ =>
      (D.trotterSum p.1.1 p.1.2).eval p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  obtain ⟨L,hL,N,hN,hbounds⟩ := D.exists_pair_speed_neighbourhood p₀.1.1 p₀.1.2
  obtain ⟨r,hrpos,hr,hp⟩ := D.exists_trotter_radius
  let T := r/(2*L)
  have hT : 0 < T := div_pos hrpos (by positivity)
  have hscale : 2*L*T ≤ r := by
    dsimp [T]
    rw [mul_div_cancel₀ _ (by positivity : 2*L ≠ 0)]
  have hc := D.trotterSum_eval_continuousOn hL.le hT.le hp hr hscale N hbounds
  obtain ⟨m,hm⟩ := exists_nat_gt (max (|p₀.2|/T) 1)
  have hm1 : (1 : ℝ) < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hmR : (0 : ℝ) < m := lt_trans zero_lt_one hm1
  let u := p₀.2/(m : ℝ)
  have hu : |u| < T := by
    rw [show |u| = |p₀.2|/(m : ℝ) by simp only [u,abs_div,abs_of_pos hmR]]
    apply (div_lt_iff₀ hmR).mpr
    nlinarith [(div_lt_iff₀ hT).mp (lt_of_le_of_lt (le_max_left _ _) hm)]
  have hopen : IsOpen {t : ℝ | |t| < T} := isOpen_lt continuous_abs continuous_const
  have hwin : {t : ℝ | |t| ≤ T} ∈ 𝓝 u :=
    Filter.mem_of_superset (hopen.mem_nhds hu)
      (fun _ ht => (show |(_ : ℝ)| < T from ht).le)
  have hS : N ×ˢ {t : ℝ | |t| ≤ T} ∈ 𝓝 (p₀.1,u) := prod_mem_nhds hN hwin
  have hsmall := hc.continuousAt hS
  have hmap : Continuous (fun p : (OneParameter G × OneParameter G) × ℝ => (p.1,p.2/(m : ℝ))) :=
    continuous_fst.prodMk (continuous_snd.div_const (m : ℝ))
  have hcomp := (hsmall.comp_of_eq (hmap.continuousAt (x := p₀)) rfl).pow m
  have he : (fun p : (OneParameter G × OneParameter G) × ℝ =>
      ((D.trotterSum p.1.1 p.1.2).eval (p.2/(m : ℝ)))^m) =
      (fun p => (D.trotterSum p.1.1 p.1.2).eval p.2) := by
    funext p
    rw [← OneParameter.eval_nat_mul,mul_div_cancel₀ _ (ne_of_gt hmR)]
  change ContinuousAt (fun p : (OneParameter G × OneParameter G) × ℝ =>
    ((D.trotterSum p.1.1 p.1.2).eval (p.2/(m : ℝ)))^m) p₀ at hcomp
  rw [he] at hcomp
  exact hcomp

/-- Trotter addition is jointly continuous in the actual compact-open
topology of continuous homomorphisms. -/
theorem continuous_trotterSum :
    Continuous (fun p : OneParameter G × OneParameter G => D.trotterSum p.1 p.2) := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  exact D.continuous_trotterSum_eval
end GleasonMetricData
end DirectedCycles
