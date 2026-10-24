import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.Metrizable.Uniformity

set_option autoImplicit false
open Filter
open scoped Topology Uniformity
namespace DirectedCycles

/-- Countability of the identity-neighbourhood filter metrizes a Hausdorff
group through its right uniformity. No invariant metric is assumed. -/
theorem group_metrizable_of_countable_nhds {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T0Space G] [(𝓝 (1 : G)).IsCountablyGenerated] :
    TopologicalSpace.MetrizableSpace G := by
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  let : (𝓤 G).IsCountablyGenerated := by
    change (Filter.comap (fun p : G × G => p.2*p.1⁻¹) (𝓝 (1 : G))).IsCountablyGenerated
    infer_instance
  exact UniformSpace.metrizableSpace

end DirectedCycles
