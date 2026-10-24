import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- A set contains no nontrivial subgroup. -/
def SubgroupFreeSet (V : Set G) : Prop :=
  ∀ H : Subgroup G, (H : Set G) ⊆ V → H = ⊥

/-- The topological no-small-subgroups property, stated by actual subgroups. -/
def HasNoSmallSubgroups (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ SubgroupFreeSet V

theorem SubgroupFreeSet.mono {V W : Set G} (hV : SubgroupFreeSet V) (hWV : W ⊆ V) :
    SubgroupFreeSet W := fun H hH => hV H (hH.trans hWV)

theorem subgroup_free_of_cyclic_nss {V : Set G}
    (hV : ∀ x : G, (∀ n : ℕ, x^n ∈ V) → x = 1) : SubgroupFreeSet V := by
  intro H hH
  apply le_antisymm _ bot_le
  intro x hx
  exact Subgroup.mem_bot.mpr (hV x (fun n => hH (H.pow_mem hx n)))

/-- Subgroup trapping expressed using an actual containing subgroup;
this does not assume that the subgroup is normal or compact. -/
def HasSubgroupTrapping (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : Set G, IsOpen U → (1 : G) ∈ U →
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
      ∃ H : Subgroup G, (H : Set G) ⊆ U ∧
        ∀ S : Subgroup G, (S : Set G) ⊆ V → S ≤ H

theorem subgroup_trapping_of_nss [TopologicalSpace G] (hnss : HasNoSmallSubgroups G) :
    HasSubgroupTrapping G := by
  obtain ⟨V,hV,hV1,hfree⟩ := hnss
  intro U _hU hU1
  refine ⟨V,hV,hV1,⊥,?_,?_⟩
  · intro x hx
    simpa only [Subgroup.mem_bot.mp hx] using hU1
  · intro S hS
    exact le_of_eq (hfree S hS)
end DirectedCycles
