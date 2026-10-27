module

public import DirectedCycles.GleasonOneParameterCompact
public import DirectedCycles.GleasonPowerDistance
public import Mathlib.Topology.DenseEmbedding

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace OneParameter
variable {G : Type*} [Group G] [TopologicalSpace G]

theorem eval_int_mul (φ : OneParameter G) (z : ℤ) (t : ℝ) :
    φ.eval ((z : ℝ)*t) = (φ.eval t)^z := by
  change φ (Multiplicative.ofAdd ((z : ℝ)*t)) = _
  rw [← zsmul_eq_mul,ofAdd_zsmul,map_zpow]
  rfl

theorem eval_rat (φ : OneParameter G) (q : ℚ) :
    φ.eval (q : ℝ) = (φ.eval (1/(q.den : ℝ)))^q.num := by
  rw [← φ.eval_int_mul,Rat.cast_def]
  congr 1
  ring

/-- Values at reciprocal positive integers determine a continuous
one-parameter subgroup, by integer powers and density of the rationals. -/
theorem eq_of_reciprocal_eq [T2Space G] (φ ψ : OneParameter G)
    (h : ∀ n : ℕ, 0 < n → φ.eval (1/(n : ℝ)) = ψ.eval (1/(n : ℝ))) : φ = ψ := by
  have hrat : (φ.eval ∘ ((↑) : ℚ → ℝ)) = (ψ.eval ∘ ((↑) : ℚ → ℝ)) := by
    funext q
    simp only [Function.comp_apply,φ.eval_rat,ψ.eval_rat,h q.den q.den_pos]
  have he : φ.eval = ψ.eval := Rat.denseRange_cast.equalizer φ.continuous_eval ψ.continuous_eval hrat
  apply ContinuousMonoidHom.ext
  intro x
  exact congrFun he x.toAdd
end OneParameter
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

include D in
/-- Evaluation at one is injective on a neighbourhood of the trivial
one-parameter subgroup. Power-distance expansion forces equality of every
small reciprocal-time root. -/
theorem exponential_locally_injective : ∃ U : Set (OneParameter G),
    U ∈ 𝓝 (1 : OneParameter G) ∧ Set.InjOn (fun φ => φ.eval 1) U := by
  let : MetricSpace G := D.compatibleMetric
  obtain ⟨r,hr,hp⟩ := D.exists_power_distance_radius
  have hC := D.constant_pos
  let R := min (1/(D.constant*(D.constant+1))) (r/(4*D.constant))
  have hR : 0 < R := by dsimp [R]; positivity
  have hscale : (D.constant+1)*R ≤ 1/D.constant := by
    have h := mul_le_mul_of_nonneg_left (min_le_left (1/(D.constant*(D.constant+1))) (r/(4*D.constant))) (by linarith : 0 ≤ D.constant+1)
    apply h.trans_eq
    field_simp
  have hspeed : 2*D.constant*R ≤ r := by
    have h := (le_div_iff₀ (show 0 < 4*D.constant by positivity)).mp (min_le_right (1/(D.constant*(D.constant+1))) (r/(4*D.constant)))
    nlinarith
  refine ⟨D.oneParameterWindow 1 R,?_,?_⟩
  · apply D.oneParameterWindow_mem_nhds
    intro t _ht
    change D.gauge (1 : G) < R
    simpa only [D.gauge_one] using hR
  · intro φ hφ ψ hψ he
    change φ.eval 1 = ψ.eval 1 at he
    apply φ.eq_of_reciprocal_eq ψ
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hbase : ∀ ζ ∈ D.oneParameterWindow 1 R,
        (n : ℝ)*D.gauge (ζ.eval (1/(n : ℝ))) ≤ r := by
      intro ζ hζ
      have h := D.oneParameter_gauge_bound ζ (by norm_num : (0 : ℝ) < 1) hR.le hscale hζ (1/(n : ℝ))
      have hh := mul_le_mul_of_nonneg_left h hnR.le
      have hid : (n : ℝ)*((2*D.constant*R/1)*|1/(n : ℝ)|) = 2*D.constant*R := by
        rw [abs_of_pos (one_div_pos.mpr hnR)]
        field_simp
      exact (hh.trans_eq hid).trans hspeed
    have hl := (hp (φ.eval (1/(n : ℝ))) (ψ.eval (1/(n : ℝ))) n hn (hbase φ hφ) (hbase ψ hψ)).1
    have hmul : (n : ℝ)*(1/(n : ℝ)) = 1 := by field_simp
    rw [← φ.eval_nat_mul,← ψ.eval_nat_mul,hmul,he,D.metric.dist_self] at hl
    have hcoef : 0 < (n : ℝ)/(2*D.constant) := by positivity
    have hz : D.metric.dist (φ.eval (1/(n : ℝ))) (ψ.eval (1/(n : ℝ))) ≤ 0 := by nlinarith
    exact D.metric.eq_of_dist_eq_zero (le_antisymm hz dist_nonneg)
end GleasonMetricData
end DirectedCycles
