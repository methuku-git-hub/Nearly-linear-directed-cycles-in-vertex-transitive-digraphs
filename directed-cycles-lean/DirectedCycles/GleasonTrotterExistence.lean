import DirectedCycles.GleasonTrotterParameterLaws
import DirectedCycles.GleasonOneParameterSpeed
import DirectedCycles.LocalPowerCurveAdditive
import DirectedCycles.ContinuousLocalCurveExtension

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace OneParameter
variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The proposed sum is an actual global continuous homomorphism and is
locally the limit of the actual finite Trotter products. -/
def IsTrotterSum (φ ψ ζ : OneParameter G) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| ≤ δ →
    Tendsto (φ.productApprox ψ t) atTop (𝓝 (ζ.eval t))

theorem IsTrotterSum.unique [T2Space G] {φ ψ ζ η : OneParameter G}
    (hζ : IsTrotterSum φ ψ ζ) (hη : IsTrotterSum φ ψ η) : ζ = η := by
  obtain ⟨δ,hδ,hζ⟩ := hζ
  obtain ⟨ε,hε,hη⟩ := hη
  apply ζ.eq_of_local_eq η (lt_min hδ hε)
  intro t ht
  exact tendsto_nhds_unique (hζ t (ht.trans (min_le_left _ _)))
    (hη t (ht.trans (min_le_right _ _)))
end OneParameter
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [IsTopologicalGroup G] [LocallyCompactSpace G]

include D in
/-- The constructed local product limit is locally additive and therefore
extends to an actual global continuous one-parameter subgroup. -/
theorem exists_trotterSum (φ ψ : OneParameter G) :
    ∃ ζ : OneParameter G, OneParameter.IsTrotterSum φ ψ ζ := by
  let : MetricSpace G := D.compatibleMetric
  obtain ⟨L₁,hL₁,hφ⟩ := D.oneParameter_exists_speed φ
  obtain ⟨L₂,hL₂,hψ⟩ := D.oneParameter_exists_speed ψ
  obtain ⟨r₀,hr₀,hp₀⟩ := D.exists_power_distance_radius
  have hC := D.constant_pos
  let r := min r₀ (1/(8*D.constant))
  have hrpos : 0 < r := lt_min hr₀ (by positivity)
  have hr : r ≤ 1/(8*D.constant) := min_le_right _ _
  have hp : ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r →
      (n : ℝ)*D.gauge h ≤ r → D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h := by
    intro g h n hn hg hh
    exact (hp₀ g h n hn (hg.trans (min_le_left _ _)) (hh.trans (min_le_left _ _))).2
  let T := r/(L₁+L₂)
  have hL : 0 < L₁+L₂ := add_pos hL₁ hL₂
  have hT : 0 < T := div_pos hrpos hL
  have hscale : (L₁+L₂)*T ≤ r := by
    dsimp [T]
    rw [mul_div_cancel₀ _ (ne_of_gt hL)]
  have hsmall : ∀ t : ℝ, |t| ≤ T → (L₁+L₂)*|t| ≤ r :=
    fun _ ht => (mul_le_mul_of_nonneg_left ht hL.le).trans hscale
  let F := φ.productLimit ψ
  have hF0 : F 0 = 1 := φ.productLimit_zero ψ
  have hcont : ContinuousOn F {t : ℝ | |t| ≤ T} :=
    D.productLimit_continuousOn hp hr φ ψ hL₁.le hφ hψ hL₂.le hT.le hscale
  have hpow : ∀ t : ℝ, ∀ n : ℕ, 0 < n → |t| ≤ T → |(n : ℝ)*t| ≤ T → F ((n : ℝ)*t) = (F t)^n := by
    intro t n hn ht hnt
    exact D.productLimit_nat_mul hp hr φ ψ hL₁.le hφ hψ t n hn (hsmall t ht) (hsmall _ hnt)
  have hinv : ∀ t : ℝ, |t| ≤ T → F (-t) = (F t)⁻¹ := by
    intro t ht
    exact D.productLimit_neg hp hr φ ψ hL₁.le hφ hψ t (hsmall t ht)
  have hadd : ∀ s t : ℝ, |s|+|t| ≤ T/2 → F (s+t) = F s*F t :=
    local_curve_add_of_power F hT hF0 hcont hpow hinv
  have hwindow : {t : ℝ | |t| ≤ T} ∈ 𝓝 (0 : ℝ) := by
    apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℝ) hT)
    intro t ht
    exact le_of_lt (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)
  have hc0 : ContinuousAt F 0 := (hcont 0 (by simp [hT.le])).continuousAt hwindow
  obtain ⟨ζ,hζ⟩ := exists_continuous_local_curve_extension F hF0 hc0 (half_pos hT) hadd
  refine ⟨ζ,T/2,half_pos hT,?_⟩
  intro t ht
  rw [hζ t ht]
  exact D.productLimit_tendsto hp hr φ ψ hL₁.le hφ hψ t (hsmall t (by linarith))

/-- Trotter addition is defined from the existence theorem, not postulated. -/
noncomputable def trotterSum (φ ψ : OneParameter G) : OneParameter G :=
  Classical.choose (D.exists_trotterSum φ ψ)

theorem trotterSum_spec (φ ψ : OneParameter G) :
    OneParameter.IsTrotterSum φ ψ (D.trotterSum φ ψ) :=
  Classical.choose_spec (D.exists_trotterSum φ ψ)
end GleasonMetricData
end DirectedCycles
