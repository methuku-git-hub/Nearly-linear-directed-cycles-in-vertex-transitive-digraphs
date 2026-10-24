import DirectedCycles.DifferentiableDoubling
import DirectedCycles.ContDiffQuadraticRemainder

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of a differentiable local multiplication at its identity is
addition, with the two summands determined by its actual identity axes. -/
theorem fderiv_local_multiplication (μ : E × E → E)
    (hμ : DifferentiableAt ℝ μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id) (p : E × E) :
    fderiv ℝ μ (0,0) p = p.1+p.2 := by
  let D := fderiv ℝ μ (0,0)
  have hD : HasFDerivAt μ D (0,0) := hμ.hasFDerivAt
  have hleftD : HasFDerivAt (fun x : E => μ (x,0)) (D.comp (ContinuousLinearMap.inl ℝ E E)) 0 :=
    hD.comp (f := fun x : E => (x,0)) 0 (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : E) (0 : E))
  have hrightD : HasFDerivAt (fun x : E => μ (0,x)) (D.comp (ContinuousLinearMap.inr ℝ E E)) 0 :=
    hD.comp (f := fun x : E => (0,x)) 0 (hasFDerivAt_prodMk_right (𝕜 := ℝ) (0 : E) (0 : E))
  have hleft : D.comp (ContinuousLinearMap.inl ℝ E E) = ContinuousLinearMap.id ℝ E :=
    hleftD.unique ((hasFDerivAt_id (𝕜 := ℝ) (0 : E)).congr_of_eventuallyEq hl)
  have hright : D.comp (ContinuousLinearMap.inr ℝ E E) = ContinuousLinearMap.id ℝ E :=
    hrightD.unique ((hasFDerivAt_id (𝕜 := ℝ) (0 : E)).congr_of_eventuallyEq hr)
  have hlx := congrArg (fun f : E →L[ℝ] E => f p.1) hleft
  have hrx := congrArg (fun f : E →L[ℝ] E => f p.2) hright
  change D (p.1,0) = p.1 at hlx
  change D (0,p.2) = p.2 at hrx
  change D p = p.1+p.2
  rw [show p = (p.1,0)+(0,p.2) by simp,D.map_add,hlx,hrx]
  simp

/-- C2 local multiplication has quadratic addition error in coordinates. -/
theorem local_multiplication_quadratic_error (μ : E × E → E)
    (hμ : ContDiffAt ℝ 2 μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id) :
    ∃ K r : ℝ, 0 ≤ K ∧ 0 < r ∧ ∀ x y : E, ‖x‖ < r → ‖y‖ < r →
      ‖μ (x,y)-x-y‖ ≤ K*(‖x‖+‖y‖)^2 := by
  have h0 : μ (0,0) = 0 := hl.self_of_nhds
  obtain ⟨K,r,hK,hr',hb⟩ := contDiffAt_quadratic_remainder μ hμ
  refine ⟨K,r,hK,hr',?_⟩
  intro x y hx hy
  have hp : ‖(x,y)‖ < r := by rw [Prod.norm_def]; exact max_lt hx hy
  have hh := hb (x,y) hp
  change ‖μ (x,y)-μ (0,0)-(fderiv ℝ μ (0,0)) (x,y)‖ ≤ K*‖(x,y)‖^2 at hh
  rw [h0,sub_zero,fderiv_local_multiplication μ (hμ.differentiableAt (by norm_num)) hl hr] at hh
  have hn : ‖(x,y)‖ ≤ ‖x‖+‖y‖ := by
    rw [Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg y)) (le_add_of_nonneg_left (norm_nonneg x))
  have hs := pow_le_pow_left₀ (norm_nonneg (x,y)) hn 2
  have he := hh.trans (mul_le_mul_of_nonneg_left hs hK)
  convert he using 1
  congr 1
  abel
end DirectedCycles
