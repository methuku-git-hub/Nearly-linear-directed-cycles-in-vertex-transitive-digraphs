import DirectedCycles.LocalGroupSmoothness
import Mathlib.Geometry.Manifold.ContMDiff.Basic

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G]

/-- Actual smooth operation germs imply all topological local-group axioms.
In particular, openness of the domain and continuity of its genuine product
are proved, not additional quotient assumptions. -/
theorem localGroupSmoothness_of_operation_germs (L : LocalGroupAlgebra G)
    (hi : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ L.inv)
    (hm : ∀ x y : G, L.Defined x y → ∃ m : G × G → G,
      ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ m (x,y) ∧
      ∀ᶠ p : G × G in 𝓝 (x,y), L.mulRel p.1 p.2 (m p)) :
    LocalGroupSmoothness (E := E) L where
  continuous_inv := hi.continuous
  isOpen_domain := by
    apply isOpen_iff_mem_nhds.2
    intro p hp
    obtain ⟨m,_,hrel⟩ := hm p.1 p.2 hp
    exact hrel.mono fun q hq => ⟨m q,hq⟩
  continuous_mul := by
    apply continuous_iff_continuousAt.2
    intro p
    obtain ⟨m,hms,hrel⟩ := hm p.val.1 p.val.2 p.property
    have hc : ContinuousAt (fun q : {q : G × G | L.Defined q.1 q.2} => m q.val) p :=
      hms.continuousAt.comp (f := Subtype.val) continuous_subtype_val.continuousAt
    apply hc.congr_of_eventuallyEq
    filter_upwards [continuous_subtype_val.continuousAt.tendsto.eventually hrel] with q hq
    exact L.unique (L.mul_spec q.val.1 q.val.2 q.property) hq
  smooth_inv := hi
  smooth_mul := hm
end DirectedCycles
