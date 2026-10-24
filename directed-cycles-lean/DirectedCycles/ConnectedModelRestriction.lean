import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
namespace DirectedCycles
variable {G H : Type*} [Group G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H]

/-- Restrict the source after choosing the quotient/model map, taking the
preimage of the identity component of its target. -/
def connectedModelRestriction (π : G →* H) :
    (Subgroup.connectedComponentOfOne H).comap π →* Subgroup.connectedComponentOfOne H where
  toFun x := ⟨π x.val,x.property⟩
  map_one' := Subtype.ext (map_one π)
  map_mul' x y := Subtype.ext (map_mul π x.val y.val)

theorem connectedModelRestriction_continuous [TopologicalSpace G] (π : G →* H) (hπ : Continuous π) :
    Continuous (connectedModelRestriction π) :=
  (hπ.comp continuous_subtype_val).subtype_mk _

theorem connectedModelRestriction_surjective (π : G →* H) (hπ : Function.Surjective π) :
    Function.Surjective (connectedModelRestriction π) := by
  intro y
  obtain ⟨x,hx⟩ := hπ y.val
  have hxS : x ∈ (Subgroup.connectedComponentOfOne H).comap π := by
    change π x ∈ Subgroup.connectedComponentOfOne H
    exact hx.symm ▸ y.property
  exact ⟨⟨x,hxS⟩,Subtype.ext hx⟩

theorem connectedModelRestriction_target_connected :
    ConnectedSpace (Subgroup.connectedComponentOfOne H) :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

theorem connectedModelRestriction_source_open [TopologicalSpace G] [LocallyConnectedSpace H]
    (π : G →* H) (hπ : Continuous π) :
    IsOpen ((Subgroup.connectedComponentOfOne H).comap π : Set G) :=
  isOpen_connectedComponent.preimage hπ

/-- Passing to the identity-component preimage preserves precisely the same
kernel in the original source; it does not choose a larger kernel. -/
theorem connectedModelRestriction_kernel (π : G →* H) :
    ((Subgroup.connectedComponentOfOne H).comap π).subtype ''
      ((connectedModelRestriction π).ker : Set ((Subgroup.connectedComponentOfOne H).comap π)) =
      (π.ker : Set G) := by
  apply Set.Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact congrArg Subtype.val hy
  · intro x hx
    have hxS : x ∈ (Subgroup.connectedComponentOfOne H).comap π := by
      change π x ∈ Subgroup.connectedComponentOfOne H
      change π x = 1 at hx
      rw [hx]
      exact (Subgroup.connectedComponentOfOne H).one_mem
    exact ⟨⟨x,hxS⟩,Subtype.ext hx,rfl⟩

/-- Compactness of the kernel is preserved under the connected restriction. -/
theorem connectedModelRestriction_kernel_compact [TopologicalSpace G]
    (π : G →* H) (hK : IsCompact (π.ker : Set G)) :
    IsCompact ((connectedModelRestriction π).ker : Set ((Subgroup.connectedComponentOfOne H).comap π)) := by
  apply Subtype.isCompact_iff.mpr
  change IsCompact (((Subgroup.connectedComponentOfOne H).comap π).subtype ''
    ((connectedModelRestriction π).ker : Set ((Subgroup.connectedComponentOfOne H).comap π)))
  rw [connectedModelRestriction_kernel]
  exact hK
end DirectedCycles
