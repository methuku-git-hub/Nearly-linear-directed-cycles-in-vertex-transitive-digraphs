module

public import DirectedCycles.GleasonOneParameterCompact
public import DirectedCycles.OneParameterOperations

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace OneParameter
variable {G : Type*} [Group G] [TopologicalSpace G]

theorem continuous_eval_pair : Continuous (fun p : OneParameter G × ℝ => p.1.eval p.2) :=
  ContinuousEval.continuous_eval

theorem continuous_scale : Continuous (fun p : ℝ × OneParameter G => scale p.1 p.2) := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous (fun p : (ℝ × OneParameter G) × Multiplicative ℝ => p.1.2.eval (p.1.1*p.2.toAdd))
  exact continuous_eval_pair.comp ((continuous_fst.snd).prodMk (continuous_fst.fst.mul continuous_snd))

theorem continuous_productApprox [IsTopologicalGroup G] (n : ℕ) :
    Continuous (fun p : (OneParameter G × OneParameter G) × ℝ =>
      p.1.1.productApprox p.1.2 p.2 n) := by
  have ha : Continuous (fun p : (OneParameter G × OneParameter G) × ℝ => p.1.1.eval (p.2/(n : ℝ))) :=
    continuous_eval_pair.comp (continuous_fst.fst.prodMk (continuous_snd.div_const (n : ℝ)))
  have hb : Continuous (fun p : (OneParameter G × OneParameter G) × ℝ => p.1.2.eval (p.2/(n : ℝ))) :=
    continuous_eval_pair.comp (continuous_fst.snd.prodMk (continuous_snd.div_const (n : ℝ)))
  exact (ha.mul hb).pow n
end OneParameter
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- A whole compact-open neighbourhood of any pair has one common global
speed bound, obtained from strict bounds on a common parameter interval. -/
theorem exists_pair_speed_neighbourhood (φ ψ : OneParameter G) :
    ∃ L : ℝ, 0 < L ∧ ∃ N : Set (OneParameter G × OneParameter G), N ∈ 𝓝 (φ,ψ) ∧
      ∀ p ∈ N, ∀ t : ℝ, D.gauge (p.1.eval t) ≤ L*|t| ∧ D.gauge (p.2.eval t) ≤ L*|t| := by
  have hC := D.constant_pos
  let R := 1/(D.constant*(D.constant+1))
  have hR : 0 < R := by dsimp [R]; positivity
  have hscale : (D.constant+1)*R ≤ 1/D.constant := by
    apply le_of_eq
    dsimp [R]
    field_simp
  obtain ⟨T₁,hT₁,hφ⟩ := D.oneParameter_exists_window φ (half_pos hR)
  obtain ⟨T₂,hT₂,hψ⟩ := D.oneParameter_exists_window ψ (half_pos hR)
  let T := min T₁ T₂
  have hT : 0 < T := lt_min hT₁ hT₂
  have hNφ : D.oneParameterWindow T R ∈ 𝓝 φ := by
    apply D.oneParameterWindow_mem_nhds
    intro t ht
    exact (hφ t (ht.trans (min_le_left _ _))).trans_lt (half_lt_self hR)
  have hNψ : D.oneParameterWindow T R ∈ 𝓝 ψ := by
    apply D.oneParameterWindow_mem_nhds
    intro t ht
    exact (hψ t (ht.trans (min_le_right _ _))).trans_lt (half_lt_self hR)
  refine ⟨2*D.constant*R/T,by positivity,
    (D.oneParameterWindow T R) ×ˢ (D.oneParameterWindow T R),prod_mem_nhds hNφ hNψ,?_⟩
  intro p hp t
  exact ⟨D.oneParameter_gauge_bound p.1 hT hR.le hscale hp.1 t,
    D.oneParameter_gauge_bound p.2 hT hR.le hscale hp.2 t⟩
end GleasonMetricData
end DirectedCycles
