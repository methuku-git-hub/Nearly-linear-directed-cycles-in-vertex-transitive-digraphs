module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The two-point error of an operator field is controlled by its deviation
from the identity and its variation between the two trajectories. -/
theorem operator_field_difference_bound (A B : E →L[ℝ] E) (v w : E) {η L : ℝ}
    (hA : ‖A-ContinuousLinearMap.id ℝ E‖ ≤ η)
    (hAB : ‖A-B‖ ≤ L*‖v-w‖) (hsmall : L*‖w‖ ≤ η) :
    ‖A v-B w-(v-w)‖ ≤ 2*η*‖v-w‖ := by
  have he : A v-B w-(v-w) =
      (A-ContinuousLinearMap.id ℝ E) (v-w)+(A-B) w := by
    simp only [sub_apply,map_sub,ContinuousLinearMap.id_apply]
    abel
  rw [he]
  have h1 := (ContinuousLinearMap.le_opNorm (A-ContinuousLinearMap.id ℝ E) (v-w)).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have h2 := (ContinuousLinearMap.le_opNorm (A-B) w).trans
    (mul_le_mul_of_nonneg_right hAB (norm_nonneg _))
  have h3 := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (v-w))
  have hh := norm_add_le ((A-ContinuousLinearMap.id ℝ E) (v-w)) ((A-B) w)
  nlinarith
end DirectedCycles
