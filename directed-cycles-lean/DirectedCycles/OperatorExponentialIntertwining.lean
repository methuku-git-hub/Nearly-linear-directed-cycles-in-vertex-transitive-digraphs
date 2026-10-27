module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Operator.Bilinear

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Intertwining bounded operators intertwines their actual convergent
exponentials, even when the intertwiner is neither square nor invertible. -/
theorem operator_exp_intertwining (T : E →L[ℝ] E) (W : F →L[ℝ] F)
    (U : E →L[ℝ] F) (h : W.comp U = U.comp T) :
    (NormedSpace.exp W).comp U = U.comp (NormedSpace.exp T) := by
  have hp (n : ℕ) : (W^n).comp U = U.comp (T^n) := by
    induction n with
    | zero => ext v; simp
    | succ n ih =>
      ext v
      change (W^(n+1)) (U v) = U ((T^(n+1)) v)
      rw [pow_succ',pow_succ']
      change W ((W^n) (U v)) = U (T ((T^n) v))
      rw [show (W^n) (U v) = U ((T^n) v) from congrArg (fun L : E →L[ℝ] F => L v) ih]
      exact congrArg (fun L : E →L[ℝ] F => L ((T^n) v)) h
  let L : (F →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) := (ContinuousLinearMap.compL ℝ E F F).flip U
  let R : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] F) := ContinuousLinearMap.compL ℝ E E F U
  have hL := L.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) W)
  have hR := R.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) T)
  have he : (fun n : ℕ => L ((n.factorial : ℝ)⁻¹ • W^n)) =
      (fun n : ℕ => R ((n.factorial : ℝ)⁻¹ • T^n)) := by
    funext n
    rw [map_smul,map_smul]
    exact congrArg (fun X : E →L[ℝ] F => (n.factorial : ℝ)⁻¹ • X) (hp n)
  rw [he] at hL
  exact hL.unique hR

end DirectedCycles
