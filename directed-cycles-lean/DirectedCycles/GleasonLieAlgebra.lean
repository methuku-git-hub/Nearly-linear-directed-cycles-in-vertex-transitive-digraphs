import DirectedCycles.GleasonOneParameterCompact
import DirectedCycles.GleasonTrotterAssociative
import Mathlib.Algebra.Module.Defs

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The actual one-parameter space with the vector operations constructed
from the compatible Gleason metric. The type wrapper records the chosen
construction without changing the underlying continuous homomorphisms. -/
def GleasonLieAlgebra (_D : GleasonMetricData G) := OneParameter G

namespace GleasonLieAlgebra
variable (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]

instance : Zero (GleasonLieAlgebra D) := ⟨(1 : OneParameter G)⟩
noncomputable instance : Add (GleasonLieAlgebra D) := ⟨D.trotterSum⟩
noncomputable instance : Neg (GleasonLieAlgebra D) := ⟨OneParameter.scale (-1)⟩

noncomputable instance : AddCommGroup (GleasonLieAlgebra D) where
  add := D.trotterSum
  zero := (1 : OneParameter G)
  neg := OneParameter.scale (-1)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := D.trotterSum_assoc
  zero_add := D.one_trotterSum
  add_zero := D.trotterSum_one
  neg_add_cancel := D.trotterSum_neg
  add_comm := D.trotterSum_comm

noncomputable instance : Module ℝ (GleasonLieAlgebra D) where
  smul := OneParameter.scale
  one_smul := OneParameter.scale_one
  mul_smul a b φ := (OneParameter.scale_mul a b φ).symm
  smul_add := D.scale_trotterSum
  add_smul := D.scale_add
  zero_smul := OneParameter.scale_zero
  smul_zero c := by
    apply ContinuousMonoidHom.ext
    intro x
    rfl

instance : TopologicalSpace (GleasonLieAlgebra D) :=
  inferInstanceAs (TopologicalSpace (OneParameter G))

/-- Forgetting the wrapper preserves exactly the original compact-open topology. -/
def toOneParameter : GleasonLieAlgebra D ≃ₜ OneParameter G := Homeomorph.refl _

instance : LocallyCompactSpace (GleasonLieAlgebra D) :=
  D.oneParameter_locallyCompact

instance : T2Space (GleasonLieAlgebra D) := by
  let : MetricSpace G := D.compatibleMetric
  exact inferInstanceAs (T2Space (OneParameter G))

end GleasonLieAlgebra
end DirectedCycles
