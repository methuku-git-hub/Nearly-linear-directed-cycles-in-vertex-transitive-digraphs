module

public import DirectedCycles.NilpotentSpanning
public import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Vanishing of all D-fold ordered products implies nilpotence of their
integral linear span. -/
theorem operator_span_nilpotent {ι V : Type*} [AddCommGroup V]
    (F : ι → Module.End ℤ V) (D : ℕ)
    (h : ∀ s : Fin D → ι, (List.ofFn (fun i => F (s i))).prod = 0) :
    (Submodule.span ℤ (Set.range F)) ^ D = ⊥ := by
  classical
  rw [Submodule.span_pow]
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  intro T hT
  obtain ⟨s,hs⟩ := Set.mem_pow.mp hT
  have hex : ∀ i : Fin D, ∃ j : ι, F j = (s i).val := fun i => (s i).property
  choose u hu using hex
  have he : (List.ofFn (fun i => F (u i))).prod = T := by
    simp_rw [hu]
    exact hs
  rw [← he,h u]
  exact Submodule.zero_mem _

/-- It suffices to check stability on the operator generators. -/
theorem operator_span_stable {ι V : Type*} [AddCommGroup V]
    (F : ι → Module.End ℤ V) (W : AddSubgroup V)
    (h : ∀ i, ∀ v ∈ W, F i v ∈ W) :
    (Submodule.span ℤ (Set.range F)) • W.toIntSubmodule ≤ W.toIntSubmodule := by
  apply Submodule.smul_le.mpr
  intro T hT v hv
  refine Submodule.span_induction (p := fun T _ => T v ∈ W) ?_ ?_ ?_ ?_ hT
  · rintro T ⟨i,rfl⟩
    exact h i v hv
  · exact W.zero_mem
  · intro S T _ _ hS hT
    exact W.add_mem hS hT
  · intro z T _ hT
    exact W.zsmul_mem hT z

end DirectedCycles
