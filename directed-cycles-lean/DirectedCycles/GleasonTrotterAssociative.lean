module

public import DirectedCycles.GleasonPowerApproximation
public import DirectedCycles.GleasonTrotterLinearLaws

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Both associations are limits of the same actual triple products.
The quadratic inner error vanishes after subdivision powers. -/
theorem trotterSum_assoc (φ ψ η : OneParameter G) :
    D.trotterSum (D.trotterSum φ ψ) η = D.trotterSum φ (D.trotterSum ψ η) := by
  let : MetricSpace G := D.compatibleMetric
  obtain ⟨L₁,hL₁,hφ⟩ := D.oneParameter_exists_speed φ
  obtain ⟨L₂,hL₂,hψ⟩ := D.oneParameter_exists_speed ψ
  obtain ⟨L₃,hL₃,hη⟩ := D.oneParameter_exists_speed η
  obtain ⟨r,hrpos,hr,hp⟩ := D.exists_trotter_radius
  have hC := D.constant_pos
  let ζ := D.trotterSum φ ψ
  let θ := D.trotterSum ψ η
  let A := D.trotterSum ζ η
  let B := D.trotterSum φ θ
  let L := L₁+L₂+L₃
  have hL : 0 < L := by dsimp [L]; positivity
  have hζ : ∀ u : ℝ, D.gauge (ζ.eval u) ≤ (L₁+L₂)*|u| :=
    D.trotterSum_gauge φ ψ hL₁.le hL₂.le hφ hψ
  have hθ : ∀ u : ℝ, D.gauge (θ.eval u) ≤ (L₂+L₃)*|u| :=
    D.trotterSum_gauge ψ η hL₂.le hL₃.le hψ hη
  have hrad : 2*r ≤ 1/D.constant := by
    have hmul := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2)
    apply hmul.trans
    field_simp
    linarith
  let f : ℝ → G := fun u => ζ.eval u*η.eval u
  let g : ℝ → G := fun u => φ.eval u*θ.eval u
  let k : ℝ → G := fun u => (φ.eval u*ψ.eval u)*η.eval u
  have hf : ∀ u : ℝ, L*|u| ≤ r → D.gauge (f u) ≤ L*|u| := by
    intro u _hu
    have hh := D.gauge_mul_le (ζ.eval u) (η.eval u)
    dsimp only [f,L]
    nlinarith [hζ u,hη u]
  have hg : ∀ u : ℝ, L*|u| ≤ r → D.gauge (g u) ≤ L*|u| := by
    intro u _hu
    have hh := D.gauge_mul_le (φ.eval u) (θ.eval u)
    dsimp only [g,L]
    nlinarith [hφ u,hθ u]
  have hk : ∀ u : ℝ, L*|u| ≤ r → D.gauge (k u) ≤ L*|u| := by
    intro u _hu
    have hh₁ := D.gauge_mul_le (φ.eval u) (ψ.eval u)
    have hh₂ := D.gauge_mul_le (φ.eval u*ψ.eval u) (η.eval u)
    dsimp only [k,L]
    nlinarith [hφ u,hψ u,hη u]
  have hef : ∀ u : ℝ, L*|u| ≤ r → D.metric.dist (f u) (k u) ≤ (8*D.constant*L₁*L₂)*|u|^2 := by
    intro u hu
    have habs := abs_nonneg u
    have hpair : (L₁+L₂)*|u| ≤ r := by dsimp only [L] at hu; nlinarith
    have hηsmall : D.gauge (η.eval u) ≤ 1/D.constant := by
      have hηr : D.gauge (η.eval u) ≤ r := by dsimp only [L] at hu; nlinarith [hη u]
      linarith
    have hxy : D.metric.dist (ζ.eval u) (φ.eval u*ψ.eval u) ≤ 1/D.constant := by
      have hh := D.dist_le_gauges (ζ.eval u) (φ.eval u*ψ.eval u)
      have hm := D.gauge_mul_le (φ.eval u) (ψ.eval u)
      nlinarith [hζ u,hφ u,hψ u]
    have he : D.metric.dist (ζ.eval u) (φ.eval u*ψ.eval u) ≤
        4*D.constant*L₁*L₂*|u|^2 := by
      rw [D.metric.dist_comm]
      simpa only [OneParameter.productApprox,Nat.cast_one,div_one,pow_one] using
        D.trotterSum_distance hp hr φ ψ hL₁.le hL₂.le hφ hψ u hpair 1 (by omega)
    have hh := D.dist_mul_right_le_two (ζ.eval u) (φ.eval u*ψ.eval u) (η.eval u) hxy hηsmall
    change D.metric.dist (ζ.eval u*η.eval u) ((φ.eval u*ψ.eval u)*η.eval u) ≤ _
    nlinarith
  have heg : ∀ u : ℝ, L*|u| ≤ r → D.metric.dist (g u) (k u) ≤ (4*D.constant*L₂*L₃)*|u|^2 := by
    intro u hu
    have hpair : (L₂+L₃)*|u| ≤ r := by dsimp only [L] at hu; nlinarith [abs_nonneg u]
    change D.metric.dist (φ.eval u*θ.eval u) ((φ.eval u*ψ.eval u)*η.eval u) ≤ _
    rw [mul_assoc,D.left_invariant,D.metric.dist_comm]
    simpa only [OneParameter.productApprox,Nat.cast_one,div_one,pow_one] using
      D.trotterSum_distance hp hr ψ η hL₂.le hL₃.le hψ hη u hpair 1 (by omega)
  obtain ⟨δ,hδ,hA⟩ := D.trotterSum_spec ζ η
  obtain ⟨ε,hε,hB⟩ := D.trotterSum_spec φ θ
  apply A.eq_of_local_eq B (lt_min (lt_min hδ hε) (div_pos hrpos hL))
  intro t ht
  have htA : |t| ≤ δ := ht.trans ((min_le_left _ _).trans (min_le_left _ _))
  have htB : |t| ≤ ε := ht.trans ((min_le_left _ _).trans (min_le_right _ _))
  have htr : L*|t| ≤ r := by
    have h := (le_div_iff₀ hL).mp (ht.trans (min_le_right _ _))
    nlinarith
  have ha : Tendsto (fun n : ℕ => (k (t/(n : ℝ)))^n) atTop (𝓝 (A.eval t)) :=
    D.powerApprox_tendsto_transfer hL.le hp f k hf hk hef htr (hA t htA)
  have hb : Tendsto (fun n : ℕ => (k (t/(n : ℝ)))^n) atTop (𝓝 (B.eval t)) :=
    D.powerApprox_tendsto_transfer hL.le hp g k hg hk heg htr (hB t htB)
  exact tendsto_nhds_unique ha hb
end GleasonMetricData
end DirectedCycles
