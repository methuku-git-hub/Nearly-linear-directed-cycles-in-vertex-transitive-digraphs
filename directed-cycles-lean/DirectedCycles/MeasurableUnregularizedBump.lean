module

public import DirectedCycles.OpenSetNormBump
public import DirectedCycles.UnregularizedEscapeBump

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [OpensMeasurableSpace G]

/-- A measurable bump with derivative controlled by unregularized
escape, once the actual product inequality has been established. -/
theorem measurable_unregularized_escape_bump {U : Set G} (hU : IsOpen U)
    (hU1 : (1 : G) ∈ U) (hUi : U⁻¹ = U) {P : ℝ} (hP : 0 < P)
    (hp : ∀ l : List G, escapeNorm U l.prod ≤ P*(l.map (escapeNorm U)).sum) :
    ∃ φ : G → ℝ, Measurable φ ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ x ∈ U, φ x = 1) ∧ (∀ x, x ∉ U^2 → φ x = 0) ∧
      (∀ g x, |φ (g⁻¹*x)-φ x| ≤ P*escapeNorm U g) := by
  let d := wordNorm (escapeNorm U)
  have hd : ∀ g, 0 ≤ d g := wordNorm_nonneg (escapeNorm_nonneg hU1)
  have hr : 0 < 1/P := by positivity
  let φ := openSetNormBump d U (1/P)
  refine ⟨φ,openSetNormBump_measurable hd ⟨1,hU1⟩ hU _,
    openSetNormBump_bounds hd ⟨1,hU1⟩ hr.le,?_,?_,?_⟩
  · intro x hx
    exact openSetNormBump_plateau hd (wordNorm_one (escapeNorm_nonneg hU1)) _ hx
  · intro x hx
    exact openSetNormBump_support ⟨1,hU1⟩ hr (fun _ hg => wordNorm_escape_separation hU1 hP hp hg) hx
  · intro g x
    have h := openSetNormBump_lipschitz hd (wordNorm_mul_le (escapeNorm_nonneg hU1))
      (wordNorm_inv (escapeNorm_inv hUi)) ⟨1,hU1⟩ hr g⁻¹ x
    have h' : |φ (g⁻¹*x)-φ x| ≤ P*d g := by
      simpa only [φ,d,wordNorm_inv (escapeNorm_inv hUi),one_div,div_inv_eq_mul,mul_comm] using h
    exact h'.trans (mul_le_mul_of_nonneg_left (wordNorm_le_weight (escapeNorm_nonneg hU1) g) hP.le)
end DirectedCycles
