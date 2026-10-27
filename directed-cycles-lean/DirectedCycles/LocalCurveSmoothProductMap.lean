module

public import DirectedCycles.LocalCurveProductDerivative
public import DirectedCycles.SmoothInverseNeighbourhood

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- An actual curve-product map has a coordinate inverse smooth on its whole
open target, using explicit smooth input domains. -/
theorem local_curve_smooth_product_map (μ : E × E → E) (S : Set (E × E))
    (hSo : IsOpen S) (hS0 : (0,0) ∈ S) (hμ0 : μ (0,0) = 0) (hμ : ContDiffOn ℝ ∞ μ S)
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id)
    (f : ℝ → E) (T : Set ℝ) (hTo : IsOpen T) (hT0 : 0 ∈ T)
    (hf0 : f 0 = 0) (hf : ContDiffOn ℝ ∞ f T)
    {v : E} (hv : HasDerivAt f v 0)
    (A : (ℝ × F) ≃L[ℝ] E) (hA : ∀ t : ℝ, A (t,0) = t • v) :
    ∃ e : OpenPartialHomeomorph (ℝ × F) E,
      (∀ p : ℝ × F, e p = μ (f p.1,A (0,p.2))) ∧
      (0 : ℝ × F) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let b : ℝ × F → E × E := fun p => (f p.1,A (0,p.2))
  let ψ : ℝ × F → E := fun p => μ (b p)
  let U : Set (ℝ × F) := {p | p.1 ∈ T ∧ b p ∈ S}
  have hA0 : A (0,0) = 0 := A.map_zero
  have hb0 : b 0 = (0,0) := by simp only [b,Prod.fst_zero,Prod.snd_zero,hf0,hA0]
  have hb : ∀ p : ℝ × F, p.1 ∈ T → ContDiffAt ℝ ∞ b p := by
    intro p hp
    exact ((hf.contDiffAt (hTo.mem_nhds hp)).comp p contDiffAt_fst).prodMk
      (A.contDiff.contDiffAt.comp p (contDiffAt_const.prodMk contDiffAt_snd))
  have hUo : IsOpen U := by
    apply isOpen_iff_mem_nhds.2
    intro p hp
    have h₁ := (continuousAt_fst : ContinuousAt (Prod.fst : ℝ × F → ℝ) p).preimage_mem_nhds (hTo.mem_nhds hp.1)
    have h₂ := (hb p hp.1).continuousAt.preimage_mem_nhds (hSo.mem_nhds hp.2)
    filter_upwards [h₁,h₂] with q hq₁ hq₂
    exact ⟨hq₁,hq₂⟩
  have hU0 : (0 : ℝ × F) ∈ U := ⟨hT0,by rw [hb0]; exact hS0⟩
  have hψ : ContDiffOn ℝ ∞ ψ U := by
    intro p hp
    exact ((hμ.contDiffAt (hSo.mem_nhds hp.2)).comp p (hb p hp.1)).contDiffWithinAt
  have hd := local_curve_product_hasFDerivAt μ ((hμ.contDiffAt (hSo.mem_nhds hS0)).differentiableAt (by simp)) hl hr f hf0 hv A hA
  obtain ⟨e,he,he0,_,hes,heis⟩ := exists_smooth_inverse_neighbourhood ψ hUo hU0 hψ A hd
  refine ⟨e,fun p => congrFun he p,he0,?_,hes,heis⟩
  rw [he]
  change μ (b 0) = 0
  rw [hb0,hμ0]
end DirectedCycles
