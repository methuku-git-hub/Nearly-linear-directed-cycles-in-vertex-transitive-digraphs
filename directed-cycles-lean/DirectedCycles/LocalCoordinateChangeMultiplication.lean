module

public import DirectedCycles.LocalMultiplicationDerivative
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A strict identity derivative transports actual local multiplication to
coordinates with addition derivative. The inverse and the local coordinate
identity are constructed by the strict inverse function theorem. -/
theorem local_coordinate_change_multiplication (F : E → E) (hF0 : F 0 = 0)
    (hF : HasStrictFDerivAt F (ContinuousLinearMap.id ℝ E) 0)
    (μ : E × E → E) (hμ : DifferentiableAt ℝ μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id) :
    ∃ ν : E × E → E, ν (0,0) = 0 ∧
      HasFDerivAt ν (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (0,0) ∧
      ∀ᶠ p : E × E in 𝓝 (0,0), F (ν p) = μ (F p.1,F p.2) := by
  have hFe : HasStrictFDerivAt F (ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap 0 := hF
  let β := hFe.localInverse F (ContinuousLinearEquiv.refl ℝ E) 0
  have hβ0 : β 0 = 0 := by simpa only [hF0] using hFe.localInverse_apply_image
  have hβ : HasFDerivAt β (ContinuousLinearMap.id ℝ E) 0 := by
    have hh : HasFDerivAt β (ContinuousLinearMap.id ℝ E) (F 0) := hFe.to_localInverse.hasFDerivAt
    simpa only [hF0] using hh
  have hμ0 : μ (0,0) = 0 := hl.self_of_nhds
  let D := ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E
  have hμD : HasFDerivAt μ D (0,0) := by
    have he : fderiv ℝ μ (0,0) = D := by
      apply ContinuousLinearMap.ext
      intro p
      exact fderiv_local_multiplication μ hμ hl hr p
    simpa only [he] using hμ.hasFDerivAt
  have hpair : HasFDerivAt (fun p : E × E => (F p.1,F p.2)) (ContinuousLinearMap.id ℝ (E × E)) (0,0) := by
    convert hF.hasFDerivAt.prodMap (p := ((0 : E),(0 : E))) hF.hasFDerivAt using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro p
      rfl
  have hμD' : HasFDerivAt μ D (F 0,F 0) := by simpa only [hF0] using hμD
  have hc : HasFDerivAt (fun p : E × E => μ (F p.1,F p.2)) D (0,0) := by
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def] using hμD'.comp (0,0) hpair
  have hβ' : HasFDerivAt β (ContinuousLinearMap.id ℝ E) (μ (F 0,F 0)) := by
    simpa only [hF0,hμ0] using hβ
  let ν : E × E → E := fun p => β (μ (F p.1,F p.2))
  have hν : HasFDerivAt ν D (0,0) := by
    simpa only [ContinuousLinearMap.id_comp,Function.comp_def,ν] using hβ'.comp (0,0) hc
  refine ⟨ν,by simp only [ν,hF0,hμ0,hβ0],hν,?_⟩
  have hright : ∀ᶠ y : E in 𝓝 0, F (β y) = y := by
    simpa only [hF0] using hFe.eventually_right_inverse
  have hct : Filter.Tendsto (fun p : E × E => μ (F p.1,F p.2)) (𝓝 (0,0)) (𝓝 0) := by
    simpa only [hF0,hμ0] using hc.continuousAt.tendsto
  exact hct.eventually hright
end DirectedCycles
