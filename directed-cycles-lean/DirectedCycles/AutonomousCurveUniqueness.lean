module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two actual local solutions of a C1 autonomous field with the same initial
value agree on a neighbourhood of their initial time. -/
theorem autonomous_curve_eventually_unique (V : E → E) (f g : ℝ → E)
    (hV : ContDiffAt ℝ 1 V (f 0)) (h0 : f 0 = g 0)
    (hf : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt f (V (f t)) t)
    (hg : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt g (V (g t)) t) : f =ᶠ[𝓝 (0 : ℝ)] g := by
  obtain ⟨K,U,hU,hLip⟩ := hV.exists_lipschitzOnWith
  have hfU : ∀ᶠ t : ℝ in 𝓝 0, f t ∈ U := (hf.self_of_nhds).continuousAt.preimage_mem_nhds hU
  have hgU : ∀ᶠ t : ℝ in 𝓝 0, g t ∈ U :=
    (hg.self_of_nhds).continuousAt.preimage_mem_nhds (by simpa only [h0] using hU)
  exact ODE_solution_unique_of_eventually (v := fun _ => V) (s := fun _ => U)
    (Filter.Eventually.of_forall fun _ => hLip) (hf.and hfU) (hg.and hgU) h0
end DirectedCycles
