import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-- A compact region containing no nontrivial entire cyclic subgroup gives
uniform finite-power trapping into every open identity neighbourhood. -/
theorem compact_power_trapping {V : Set G} (hV : IsCompact V)
    (hNSS : ∀ x : G, (∀ n : ℕ, x^n ∈ V) → x = 1)
    {W : Set G} (hW : IsOpen W) (hW1 : (1 : G) ∈ W) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ x : G, (∀ n ≤ M, x^n ∈ V) → x ∈ W := by
  classical
  let U := fun n : ℕ => W ∪ {x : G | x^n ∉ V}
  have hU : ∀ n, IsOpen (U n) := by
    intro n
    exact hW.union ((hV.isClosed.preimage (continuous_pow n)).isOpen_compl)
  have hcover : V ⊆ ⋃ n, U n := by
    intro x _
    by_cases hx : x ∈ W
    · exact Set.mem_iUnion.mpr ⟨0,Or.inl hx⟩
    · have hn : ∃ n : ℕ, x^n ∉ V := by
        by_contra h
        have hall : ∀ n : ℕ, x^n ∈ V := by simpa using h
        exact hx ((hNSS x hall).symm ▸ hW1)
      obtain ⟨n,hn⟩ := hn
      exact Set.mem_iUnion.mpr ⟨n,Or.inr hn⟩
  obtain ⟨I,hI⟩ := hV.elim_finite_subcover U hU hcover
  refine ⟨max 1 (I.sup id),le_max_left _ _,?_⟩
  intro x hx
  have hxV : x ∈ V := by simpa using hx 1 (le_max_left _ _)
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (hI hxV)
  obtain ⟨hnI,hnU⟩ := Set.mem_iUnion.mp hn
  rcases hnU with hxW | hxnot
  · exact hxW
  · exact (hxnot (hx n ((Finset.le_sup (f := id) hnI).trans (le_max_right _ _)))).elim
end DirectedCycles
