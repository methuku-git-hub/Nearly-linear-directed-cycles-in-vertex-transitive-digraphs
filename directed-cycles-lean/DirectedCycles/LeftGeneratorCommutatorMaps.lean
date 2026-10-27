module

public import DirectedCycles.LeftGeneratorCommutators

@[expose] public section

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

theorem leftGeneratorCommutator_mem {α G : Type*} [Group G] (g : α → G) (i : α) (l : List α) :
    leftGeneratorCommutator g i l ∈ iteratedGeneratorCommutators (Set.range g) l.length := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨i,rfl⟩
  | append_singleton l j ih =>
    rw [leftGeneratorCommutator_append]
    simp only [List.length_append,List.length_cons,List.length_nil]
    exact ⟨_,ih,g j,⟨j,rfl⟩,rfl⟩

theorem map_leftGeneratorCommutator {α G H : Type*} [Group G] [Group H]
    (f : G →* H) (g : α → G) (i : α) (l : List α) :
    f (leftGeneratorCommutator g i l) = leftGeneratorCommutator (fun j => f (g j)) i l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l j ih =>
    rw [leftGeneratorCommutator_append,leftGeneratorCommutator_append,map_commutatorElement,ih]
end DirectedCycles
