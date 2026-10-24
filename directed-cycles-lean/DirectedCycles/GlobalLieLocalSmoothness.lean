import DirectedCycles.LocalGroupSmoothness
import Mathlib.Geometry.Manifold.Algebra.LieGroup

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles

/-- A genuine global Lie group supplies the precise smooth local algebra
used by the dimension induction. -/
theorem global_lie_local_smoothness {H E : Type*} [Group H] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E H]
    [LieGroup 𝓘(ℝ,E) ∞ H] :
    LocalGroupSmoothness (E := E) (LocalGroupAlgebra.ofGroup H) := by
  let : IsTopologicalGroup H := topologicalGroup_of_lieGroup (I := 𝓘(ℝ,E)) (n := ∞)
  exact {
    toLocalGroupTopology := LocalGroupTopology.ofGroup
    smooth_inv := contMDiff_inv 𝓘(ℝ,E) ∞
    smooth_mul := by
      intro x y _
      exact ⟨fun p => p.1*p.2,(contMDiff_mul 𝓘(ℝ,E) ∞).contMDiffAt,Filter.Eventually.of_forall (fun _ => rfl)⟩ }
end DirectedCycles
