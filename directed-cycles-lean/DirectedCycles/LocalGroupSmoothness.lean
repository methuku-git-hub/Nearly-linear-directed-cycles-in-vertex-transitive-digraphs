module

public import DirectedCycles.LocalGroupTopology
public import Mathlib.Geometry.Manifold.ContMDiff.Defs

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G]

/-- Smooth local-group operations on their actual domain. Near each defined
pair, a smooth local product agrees with the functional multiplication relation;
undefined pairs are not assigned a mathematical multiplication law. -/
structure LocalGroupSmoothness (L : LocalGroupAlgebra G) : Prop extends LocalGroupTopology L where
  smooth_inv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ L.inv
  smooth_mul : ∀ x y : G, L.Defined x y → ∃ m : G × G → G,
    ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ m (x,y) ∧
    ∀ᶠ p : G × G in 𝓝 (x,y), L.mulRel p.1 p.2 (m p)
end DirectedCycles
