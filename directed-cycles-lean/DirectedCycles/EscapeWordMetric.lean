module

public import DirectedCycles.EscapeWordGauge

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Topology Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-- The distance formula has exactly the original topology, as witnessed
by two proved cofinality statements for its identity balls. -/
theorem escape_word_metric_open_iff {U : Set G} (hU : IsOpen U)
    (hU1 : (1 : G) ∈ U) (hUc : IsCompact (closure U))
    (hNSS : ∀ x : G, (∀ n : ℕ, x^n ∈ closure U) → x = 1)
    {D : ℝ} (hD : 0 < D)
    (hprod : ∀ l : List G, escapeNorm U l.prod ≤ D*(l.map (escapeNorm U)).sum)
    (S : Set G) : IsOpen S ↔
      ∀ x ∈ S, ∃ ε > 0, ∀ y, escapeWordGauge U (x⁻¹*y) < ε → y ∈ S := by
  constructor
  · intro hS x hx
    have hpre : IsOpen ((fun y => x*y) ⁻¹' S) := hS.preimage (continuous_const.mul continuous_id)
    have hpre1 : (1 : G) ∈ (fun y => x*y) ⁻¹' S := by simpa using hx
    obtain ⟨ε,hε,hball⟩ := escapeWordGauge_ball_subset hU1 hUc hNSS hD hprod hpre hpre1
    refine ⟨ε,hε,?_⟩
    intro y hy
    have h := hball hy
    simpa only [Set.mem_preimage,mul_inv_cancel_left] using h
  · intro hS
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨ε,hε,hball⟩ := hS x hx
    have hmap : Tendsto (fun y : G => x⁻¹*y) (𝓝 x) (𝓝 (1 : G)) := by
      have ht : Continuous (fun y : G => x⁻¹*y) := continuous_const.mul continuous_id
      simpa only [inv_mul_cancel] using ht.tendsto x
    exact Filter.mem_of_superset (hmap (escapeWordGauge_ball_mem_nhds hU hU1 hε)) hball

/-- A genuine left-invariant metric on the supplied topology, constructed
from the unregularized escape word norm. -/
@[instance_reducible]
noncomputable def escapeWordMetric {U : Set G} (hU : IsOpen U)
    (hU1 : (1 : G) ∈ U) (hUi : U⁻¹ = U) (hUc : IsCompact (closure U))
    (hNSS : ∀ x : G, (∀ n : ℕ, x^n ∈ closure U) → x = 1)
    {D : ℝ} (hD : 0 < D)
    (hprod : ∀ l : List G, escapeNorm U l.prod ≤ D*(l.map (escapeNorm U)).sum) : MetricSpace G :=
  MetricSpace.ofDistTopology (fun x y => escapeWordGauge U (x⁻¹*y))
    (fun x => by rw [inv_mul_cancel,escapeWordGauge_one hU1])
    (fun x y => by
      have h := escapeWordGauge_inv hUi (x⁻¹*y)
      simpa only [mul_inv_rev,inv_inv] using h.symm)
    (fun x y z => by
      have h := escapeWordGauge_mul_le hU1 (x⁻¹*y) (y⁻¹*z)
      simpa only [mul_assoc,mul_inv_cancel_left] using h)
    (escape_word_metric_open_iff hU hU1 hUc hNSS hD hprod)
    (fun x y h => by
      have he := escapeWordGauge_eq_zero_imp hU1
        (fun g hg => hNSS g (fun n => subset_closure (hg n))) hD hprod h
      exact inv_mul_eq_one.mp he)

theorem escapeWordMetric_dist {U : Set G} (hU : IsOpen U)
    (hU1 : (1 : G) ∈ U) (hUi : U⁻¹ = U) (hUc : IsCompact (closure U))
    (hNSS : ∀ x : G, (∀ n : ℕ, x^n ∈ closure U) → x = 1)
    {D : ℝ} (hD : 0 < D)
    (hprod : ∀ l : List G, escapeNorm U l.prod ≤ D*(l.map (escapeNorm U)).sum) (x y : G) :
    (escapeWordMetric hU hU1 hUi hUc hNSS hD hprod).dist x y = escapeWordGauge U (x⁻¹*y) := rfl

theorem escapeWordMetric_topology {U : Set G} (hU : IsOpen U)
    (hU1 : (1 : G) ∈ U) (hUi : U⁻¹ = U) (hUc : IsCompact (closure U))
    (hNSS : ∀ x : G, (∀ n : ℕ, x^n ∈ closure U) → x = 1)
    {D : ℝ} (hD : 0 < D)
    (hprod : ∀ l : List G, escapeNorm U l.prod ≤ D*(l.map (escapeNorm U)).sum) :
    (escapeWordMetric hU hU1 hUi hUc hNSS hD hprod).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace G) := rfl

theorem escapeWordMetric_left_invariant {U : Set G} (hU : IsOpen U)
    (hU1 : (1 : G) ∈ U) (hUi : U⁻¹ = U) (hUc : IsCompact (closure U))
    (hNSS : ∀ x : G, (∀ n : ℕ, x^n ∈ closure U) → x = 1)
    {D : ℝ} (hD : 0 < D)
    (hprod : ∀ l : List G, escapeNorm U l.prod ≤ D*(l.map (escapeNorm U)).sum) (a x y : G) :
    (escapeWordMetric hU hU1 hUi hUc hNSS hD hprod).dist (a*x) (a*y) =
      (escapeWordMetric hU hU1 hUi hUc hNSS hD hprod).dist x y := by
  simp only [escapeWordMetric_dist,mul_inv_rev,mul_assoc,inv_mul_cancel_left]
end DirectedCycles
