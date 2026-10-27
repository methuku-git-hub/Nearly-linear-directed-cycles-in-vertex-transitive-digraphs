module

public import DirectedCycles.GleasonTrotterExistence
public import DirectedCycles.OneParameterOperations

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace OneParameter
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- The identity subgroup is an actual additive identity for Trotter limits. -/
theorem isTrotterSum_one (φ : OneParameter G) : IsTrotterSum φ 1 φ := by
  refine ⟨1,by norm_num,?_⟩
  intro t _ht
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (φ.productApprox_one t n (by omega)).symm

/-- Exchanging the two factors changes each product by a conjugation that
tends to the identity. -/
theorem IsTrotterSum.comm {φ ψ ζ : OneParameter G} (h : IsTrotterSum φ ψ ζ) :
    IsTrotterSum ψ φ ζ := by
  obtain ⟨δ,hδ,h⟩ := h
  refine ⟨δ,hδ,?_⟩
  intro t ht
  have hy : Tendsto (fun n : ℕ => ψ.eval (t/(n : ℝ))) atTop (𝓝 (1 : G)) := by
    simpa only [Function.comp_def,ψ.eval_zero] using ψ.continuous_eval.continuousAt.tendsto.comp
      (tendsto_const_div_atTop_nhds_zero_nat t)
  have hh := (hy.mul (h t ht)).mul hy.inv
  simp only [one_mul,inv_one,mul_one] at hh
  have he : (ψ.productApprox φ t) =
      (fun n : ℕ => ψ.eval (t/(n : ℝ))*φ.productApprox ψ t n*(ψ.eval (t/(n : ℝ)))⁻¹) :=
    funext (fun n => φ.productApprox_swap ψ t n)
  rw [he]
  exact hh

omit [IsTopologicalGroup G] in
/-- Reparameterisation commutes with the actual local product limit. -/
theorem IsTrotterSum.scale {φ ψ ζ : OneParameter G} (h : IsTrotterSum φ ψ ζ) (c : ℝ) :
    IsTrotterSum (OneParameter.scale c φ) (OneParameter.scale c ψ) (OneParameter.scale c ζ) := by
  obtain ⟨δ,hδ,h⟩ := h
  have hc : 0 < |c|+1 := by positivity
  refine ⟨δ/(|c|+1),div_pos hδ hc,?_⟩
  intro t ht
  have hct : |c*t| ≤ δ := by
    rw [abs_mul]
    have ht' := (le_div_iff₀ hc).mp ht
    nlinarith [abs_nonneg t]
  have he : (OneParameter.scale c φ).productApprox (OneParameter.scale c ψ) t = φ.productApprox ψ (c*t) :=
    funext (fun n => productApprox_scale c φ ψ t n)
  rw [he,scale_eval]
  exact h (c*t) hct

omit [IsTopologicalGroup G] in
/-- Scalar addition for the same subgroup is already exact at each
positive finite subdivision. -/
theorem isTrotterSum_same_scales (a b : ℝ) (φ : OneParameter G) :
    IsTrotterSum (scale a φ) (scale b φ) (scale (a+b) φ) := by
  refine ⟨1,by norm_num,?_⟩
  intro t _ht
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (productApprox_same_scales a b φ t n (by omega)).symm
end OneParameter
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [IsTopologicalGroup G] [LocallyCompactSpace G]

theorem trotterSum_one (φ : OneParameter G) : D.trotterSum φ 1 = φ := by
  let : MetricSpace G := D.compatibleMetric
  exact (D.trotterSum_spec φ 1).unique (φ.isTrotterSum_one)

theorem trotterSum_comm (φ ψ : OneParameter G) : D.trotterSum φ ψ = D.trotterSum ψ φ := by
  let : MetricSpace G := D.compatibleMetric
  exact (D.trotterSum_spec φ ψ).unique (D.trotterSum_spec ψ φ).comm

theorem one_trotterSum (φ : OneParameter G) : D.trotterSum 1 φ = φ := by
  rw [D.trotterSum_comm,D.trotterSum_one]

theorem scale_trotterSum (c : ℝ) (φ ψ : OneParameter G) :
    OneParameter.scale c (D.trotterSum φ ψ) =
      D.trotterSum (OneParameter.scale c φ) (OneParameter.scale c ψ) := by
  let : MetricSpace G := D.compatibleMetric
  exact ((D.trotterSum_spec φ ψ).scale c).unique (D.trotterSum_spec _ _)

theorem scale_add (a b : ℝ) (φ : OneParameter G) :
    OneParameter.scale (a+b) φ = D.trotterSum (OneParameter.scale a φ) (OneParameter.scale b φ) := by
  let : MetricSpace G := D.compatibleMetric
  exact (OneParameter.isTrotterSum_same_scales a b φ).unique (D.trotterSum_spec _ _)

theorem trotterSum_neg (φ : OneParameter G) :
    D.trotterSum (OneParameter.scale (-1) φ) φ = 1 := by
  have h := (D.scale_add (-1) 1 φ).symm
  simpa only [neg_add_cancel,OneParameter.scale_zero,OneParameter.scale_one] using h
end GleasonMetricData
end DirectedCycles
