module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An identity derivative gives explicit two-sided local norm comparison. -/
theorem identity_derivative_norm_bounds (F : E → E) (hF0 : F 0 = 0)
    (hF : HasFDerivAt F (ContinuousLinearMap.id ℝ E) 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      (1-ε)*‖x‖ ≤ ‖F x‖ ∧ ‖F x‖ ≤ (1+ε)*‖x‖ := by
  have he := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hF).bound hε
  have he' : ∀ᶠ x : E in 𝓝 0, ‖F x-x‖ ≤ ε*‖x‖ := by
    simpa only [zero_add,hF0,sub_zero,ContinuousLinearMap.id_apply] using he
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp he'
  refine ⟨r,hr,?_⟩
  intro x hx
  have herr : ‖F x-x‖ ≤ ε*‖x‖ := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hx)
  have hupper := norm_le_insert' (F x) x
  have hlower := norm_le_insert' x (F x)
  rw [norm_sub_rev x (F x)] at hlower
  constructor <;> nlinarith

/-- The strict inverse function theorem supplies an inverse germ with
identity derivative, both exact inverse identities, and value zero. -/
theorem strict_identity_local_inverse [CompleteSpace E] (F : E → E) (hF0 : F 0 = 0)
    (hF : HasStrictFDerivAt F (ContinuousLinearMap.id ℝ E) 0) :
    ∃ β : E → E, β 0 = 0 ∧ HasFDerivAt β (ContinuousLinearMap.id ℝ E) 0 ∧
      (∀ᶠ y : E in 𝓝 0, F (β y) = y) ∧ (∀ᶠ x : E in 𝓝 0, β (F x) = x) := by
  have hFe : HasStrictFDerivAt F (ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap 0 := hF
  let β := hFe.localInverse F (ContinuousLinearEquiv.refl ℝ E) 0
  have hβ0 : β 0 = 0 := by simpa only [hF0] using hFe.localInverse_apply_image
  have hβ : HasFDerivAt β (ContinuousLinearMap.id ℝ E) 0 := by
    have hh : HasFDerivAt β (ContinuousLinearMap.id ℝ E) (F 0) := hFe.to_localInverse.hasFDerivAt
    simpa only [hF0] using hh
  exact ⟨β,hβ0,hβ,by simpa only [hF0] using hFe.eventually_right_inverse,hFe.eventually_left_inverse⟩
end DirectedCycles
