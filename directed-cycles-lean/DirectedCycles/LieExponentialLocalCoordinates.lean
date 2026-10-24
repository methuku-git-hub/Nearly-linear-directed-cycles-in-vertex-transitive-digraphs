import DirectedCycles.LieExponentialStrictDerivative
import DirectedCycles.LieExponentialContinuity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- The constructed exponential has actual local inverse coordinates at the
identity. Its source and target are open, and its forward map agrees with the
actual exponential throughout its source. -/
theorem lie_exponential_local_coordinates :
    ∃ a : OpenPartialHomeomorph E G, (0 : E) ∈ a.source ∧ a 0 = 1 ∧
      (∀ v ∈ a.source, a v = lieExponential (G := G) v) := by
  let e := chartAt E (1 : G)
  let c : E := e 1
  let F : E → E := fun v => e (lieExponential (G := G) v)-c
  have h1 : (1 : G) ∈ e.source := mem_chart_source E 1
  have hc : c ∈ e.target := e.mapsTo h1
  have hF0 : F 0 = 0 := by simp only [F,lieExponential_zero,c,sub_self]
  have hD : HasStrictFDerivAt F (ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap 0 :=
    lie_exponential_coordinate_strict_derivative (G := G) (E := E)
  let b := hD.toOpenPartialHomeomorph F
  have hb0 : (0 : E) ∈ b.source := hD.mem_toOpenPartialHomeomorph_source
  have hbzero : b 0 = 0 := hF0
  let a := (b.trans (Homeomorph.addRight c).toOpenPartialHomeomorph).trans e.symm
  have ha0 : (0 : E) ∈ a.source := by
    change ((0 : E) ∈ b.source ∧ b 0 ∈ Set.univ) ∧ b 0+c ∈ e.target
    exact ⟨⟨hb0,Set.mem_univ _⟩,by rw [hbzero,zero_add]; exact hc⟩
  have ha1 : a 0 = 1 := by
    change e.symm (b 0+c) = 1
    rw [hbzero,zero_add]
    exact e.left_inv h1
  let U := (lieExponential (G := G) (E := E)) ⁻¹' e.source
  have hUo : IsOpen U := e.open_source.preimage (lie_exponential_continuous (G := G) (E := E))
  have hU0 : (0 : E) ∈ U := by simpa only [U,Set.mem_preimage,lieExponential_zero] using h1
  let a' := a.restr U
  have hsource : a'.source = a.source ∩ U := by
    exact congrArg (fun S : Set E => a.source ∩ S) hUo.interior_eq
  refine ⟨a',?_,ha1,?_⟩
  · rw [hsource]
    exact ⟨ha0,hU0⟩
  · intro v hv
    have hvU : lieExponential (G := G) v ∈ e.source := (hsource ▸ hv).2
    change e.symm (F v+c) = lieExponential (G := G) v
    dsimp only [F]
    rw [sub_add_cancel]
    exact e.left_inv hvU
end DirectedCycles
