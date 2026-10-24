import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A C1 operator field supplies a common local Lipschitz constant for all
vector fields obtained by evaluating it on the unit ball of parameters. -/
theorem exists_uniform_operator_field_lipschitz (A : E → E →L[ℝ] E)
    (hA : ContDiffAt ℝ 1 A 0) :
    ∃ K : NNReal, ∃ S : Set E, S ∈ 𝓝 (0 : E) ∧
      ∀ v : E, ‖v‖ ≤ 1 → LipschitzOnWith K (fun x => A x v) S := by
  obtain ⟨K,S,hS,hLip⟩ := hA.exists_lipschitzOnWith
  refine ⟨K,S,hS,?_⟩
  intro v hv
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm]
  calc
    ‖A x v-A y v‖ = ‖(A x-A y) v‖ := rfl
    _ ≤ ‖A x-A y‖*‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖A x-A y‖ := by nlinarith [norm_nonneg (A x-A y)]
    _ ≤ (K : ℝ)*dist x y := by simpa only [dist_eq_norm] using hLip.dist_le_mul x hx y hy
end DirectedCycles
