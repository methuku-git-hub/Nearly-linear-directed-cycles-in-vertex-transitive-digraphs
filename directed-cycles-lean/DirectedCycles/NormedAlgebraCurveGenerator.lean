import DirectedCycles.NormedAlgebraOneParameter
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
/-- The derivative at zero determines the entire actual multiplicative
curve in a Banach algebra. -/
theorem normedAlgebra_curve_hasDerivAt (φ : ℝ → A)
    (hm : ∀ s t, φ (s+t) = φ s*φ t) {v : A} (hv : HasDerivAt φ v 0) (t : ℝ) :
    HasDerivAt φ (φ t*v) t := by
  have hshift : HasDerivAt (fun s : ℝ => s-t) 1 t := (hasDerivAt_id t).sub_const t
  have hφ : HasDerivAt (fun s : ℝ => φ (s-t)) v t := by
    simpa only [Function.comp_def,one_smul] using hv.scomp_of_eq t hshift (sub_self t).symm
  apply (hφ.const_mul (φ t)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun s => by simpa only [add_sub_cancel] using hm t (s-t))

/-- Solving the actual constant-coefficient derivative equation by a
product with the inverse exponential gives the generator formula. -/
theorem normedAlgebra_curve_eq_exp (φ : ℝ → A) (h0 : φ 0 = 1)
    (hm : ∀ s t, φ (s+t) = φ s*φ t) {v : A} (hv : HasDerivAt φ v 0) :
    ∀ t : ℝ, φ t = NormedSpace.exp (t • v) := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  let f := fun t : ℝ => φ t*NormedSpace.exp (t • (-v))
  have hd : ∀ t : ℝ, HasDerivAt f 0 t := by
    intro t
    have h := (normedAlgebra_curve_hasDerivAt φ hm hv t).mul
      (hasDerivAt_exp_smul_const' (-v) t)
    convert h using 1
    simp only [mul_neg,neg_mul,mul_assoc,add_neg_cancel]
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv)
  intro t
  have ht : φ t*NormedSpace.exp (-(t • v)) = 1 := by
    simpa only [f,smul_neg,zero_smul,neg_zero,NormedSpace.exp_zero,h0,one_mul] using hc t 0
  have h := congrArg (fun z : A => z*NormedSpace.exp (t • v)) ht
  have hexp : NormedSpace.exp (-(t • v))*NormedSpace.exp (t • v) = (1 : A) := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl (t • v)).neg_left,neg_add_cancel,NormedSpace.exp_zero]
  simpa only [mul_assoc,hexp,mul_one,one_mul] using h

/-- Every continuous one-parameter curve in a Banach algebra has its
constructed generator; no matrix logarithm or differentiability is assumed. -/
theorem normedAlgebra_one_parameter_generator (φ : ℝ → A) (h0 : φ 0 = 1)
    (hc : ContinuousAt φ 0) (hm : ∀ s t, φ (s+t) = φ s*φ t) :
    ∃ v : A, HasDerivAt φ v 0 ∧ ∀ t : ℝ, φ t = NormedSpace.exp (t • v) := by
  have hd := (normedAlgebra_one_parameter_contDiffAt_zero φ h0 hc hm).differentiableAt (by simp)
  exact ⟨deriv φ 0,hd.hasDerivAt,normedAlgebra_curve_eq_exp φ h0 hm hd.hasDerivAt⟩

end DirectedCycles
