module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An actual smooth map on an open neighbourhood with invertible derivative
has a local inverse smooth throughout its target. The neighbourhood is obtained
from openness of invertible derivatives, so no uniform C-infinity neighbourhood
is incorrectly inferred from smoothness merely at one point. -/
theorem exists_smooth_inverse_neighbourhood (f : E → F) {U : Set E}
    (hU : IsOpen U) (h0 : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (A : E ≃L[ℝ] F) (hd : HasFDerivAt f A.toContinuousLinearMap 0) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ (0 : E) ∈ e.source ∧
      e.source ⊆ U ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hf0 : ContDiffAt ℝ ∞ f 0 := hf.contDiffAt (hU.mem_nhds h0)
  have hcD := hf0.continuousAt_fderiv (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hnear : {x : E | fderiv ℝ f x ∈ Set.range (fun B : E ≃L[ℝ] F => B.toContinuousLinearMap)} ∈ 𝓝 (0 : E) := by
    apply hcD.preimage_mem_nhds
    rw [hd.fderiv]
    exact A.nhds
  obtain ⟨O,hO,hOo,hO0⟩ := mem_nhds_iff.1 hnear
  let b := hf0.toOpenPartialHomeomorph f hd (by simp)
  let e := b.restr (U ∩ O)
  have hsource : e.source = b.source ∩ (U ∩ O) := by
    exact congrArg (fun S : Set E => b.source ∩ S) (hU.inter hOo).interior_eq
  have hb0 : (0 : E) ∈ b.source := hf0.mem_toOpenPartialHomeomorph_source hd (by simp)
  have he0 : (0 : E) ∈ e.source := by rw [hsource]; exact ⟨hb0,h0,hO0⟩
  have heU : e.source ⊆ U := by rw [hsource]; exact fun x hx => hx.2.1
  have heO : e.source ⊆ O := by rw [hsource]; exact fun x hx => hx.2.2
  have hefun : (e : E → F) = f := rfl
  have heSmooth : ContDiffOn ℝ ∞ e e.source := by
    rw [hefun]
    exact hf.mono heU
  refine ⟨e,hefun,he0,heU,heSmooth,?_⟩
  intro y hy
  have hx : e.symm y ∈ e.source := e.symm.mapsTo hy
  have hfx : ContDiffAt ℝ ∞ f (e.symm y) := hf.contDiffAt (hU.mem_nhds (heU hx))
  obtain ⟨B,hB⟩ := hO (heO hx)
  change B.toContinuousLinearMap = fderiv ℝ f (e.symm y) at hB
  have hder : HasFDerivAt e B.toContinuousLinearMap (e.symm y) := by
    rw [hefun,hB]
    exact (hfx.differentiableAt (by simp)).hasFDerivAt
  exact (e.contDiffAt_symm hy hder (by rw [hefun]; exact hfx)).contDiffWithinAt
end DirectedCycles
