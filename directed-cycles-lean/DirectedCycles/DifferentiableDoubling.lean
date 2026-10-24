import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A differentiable multiplication with local identity axes has derivative
addition at the origin. Its diagonal therefore has derivative twice the
identity. Only the actual local identity identities are used. -/
theorem hasFDerivAt_diagonal_twice (μ : E × E → E)
    (hμ : DifferentiableAt ℝ μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id) :
    HasFDerivAt (fun x => μ (x,x)) ((2 : ℝ) • ContinuousLinearMap.id ℝ E) 0 := by
  let D := fderiv ℝ μ (0,0)
  have hD : HasFDerivAt μ D (0,0) := hμ.hasFDerivAt
  have hleftD : HasFDerivAt (fun x : E => μ (x,0)) (D.comp (ContinuousLinearMap.inl ℝ E E)) 0 :=
    hD.comp (f := fun x : E => (x,0)) (0 : E) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : E) (0 : E))
  have hrightD : HasFDerivAt (fun x : E => μ (0,x)) (D.comp (ContinuousLinearMap.inr ℝ E E)) 0 :=
    hD.comp (f := fun x : E => (0,x)) (0 : E) (hasFDerivAt_prodMk_right (𝕜 := ℝ) (0 : E) (0 : E))
  have hleft : D.comp (ContinuousLinearMap.inl ℝ E E) = ContinuousLinearMap.id ℝ E :=
    hleftD.unique ((hasFDerivAt_id (𝕜 := ℝ) (0 : E)).congr_of_eventuallyEq hl)
  have hright : D.comp (ContinuousLinearMap.inr ℝ E E) = ContinuousLinearMap.id ℝ E :=
    hrightD.unique ((hasFDerivAt_id (𝕜 := ℝ) (0 : E)).congr_of_eventuallyEq hr)
  have hdiag : D.comp ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)) =
      (2 : ℝ) • ContinuousLinearMap.id ℝ E := by
    ext x
    have hlx := congrArg (fun f : E →L[ℝ] E => f x) hleft
    have hrx := congrArg (fun f : E →L[ℝ] E => f x) hright
    change D (x,0) = x at hlx
    change D (0,x) = x at hrx
    change D (x,x) = (2 : ℝ) • x
    rw [show (x,x) = (x,0)+(0,x) by simp,D.map_add,hlx,hrx,two_smul]
  have hh := hD.comp (f := fun x : E => (x,x)) 0 ((hasFDerivAt_id (𝕜 := ℝ) (0 : E)).prodMk (hasFDerivAt_id 0))
  rw [hdiag] at hh
  exact hh

/-- Twice-identity derivative gives a genuine expanding neighbourhood. -/
theorem exists_doubling_expansion (f : E → E) (hf0 : f 0 = 0)
    (hf : HasFDerivAt f ((2 : ℝ) • ContinuousLinearMap.id ℝ E) 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : E, ‖x‖ < r → (3/2 : ℝ)*‖x‖ ≤ ‖f x‖ := by
  have hsmall := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hf).bound (show (0 : ℝ) < 1/2 by norm_num)
  have hbound : ∀ᶠ x in 𝓝 (0 : E), ‖f x-(2 : ℝ) • x‖ ≤ (1/2 : ℝ)*‖x‖ := by
    simpa only [zero_add,hf0,sub_zero,smul_apply,ContinuousLinearMap.id_apply] using hsmall
  obtain ⟨r,hr,hrbound⟩ := Metric.mem_nhds_iff.mp hbound
  refine ⟨r,hr,?_⟩
  intro x hx
  have he := hrbound (by simpa only [Metric.mem_ball,dist_zero_right] using hx)
  change ‖f x-(2 : ℝ) • x‖ ≤ (1/2 : ℝ)*‖x‖ at he
  have htri : ‖(2 : ℝ) • x‖ ≤ ‖f x‖+‖f x-(2 : ℝ) • x‖ := by
    calc
      ‖(2 : ℝ) • x‖ = ‖f x-(f x-(2 : ℝ) • x)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖f x‖+‖f x-(2 : ℝ) • x‖ := norm_sub_le _ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
  linarith
end DirectedCycles
