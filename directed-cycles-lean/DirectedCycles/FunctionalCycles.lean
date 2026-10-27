module

public import DirectedCycles.StrongCycleExistence

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- In a functional digraph a cycle cannot have an edge leaving its vertices. -/
theorem Cycle.range_closed_of_functional {V : Type*} {D : Digraph V} (C : Cycle D)
    (hf : ∀ x y z, D x y → D x z → y = z) {x y : V}
    (hx : x ∈ Set.range C.vertex) (hxy : D x y) : y ∈ Set.range C.vertex := by
  obtain ⟨i,rfl⟩ := hx
  exact ⟨finRotate C.length i,hf _ _ _ (C.arc i) hxy⟩

/-- Every cycle of a strongly connected functional digraph is Hamiltonian. -/
theorem Cycle.surjective_of_functional_strong {V : Type*} {D : Digraph V} (C : Cycle D)
    (hf : ∀ x y z, D x y → D x z → y = z) (hsc : StronglyConnected D) :
    Function.Surjective C.vertex := by
  let i : Fin C.length := ⟨0,by have := C.two_le; omega⟩
  intro x
  have hr := hsc (C.vertex i) x
  have hx : ∀ {u v}, Reachable D u v → u ∈ Set.range C.vertex → v ∈ Set.range C.vertex := by
    intro u v h hu
    induction h with
    | refl => exact hu
    | tail h huv ih => exact C.range_closed_of_functional hf ih huv
  exact hx hr ⟨i,rfl⟩

theorem functional_strong_cycle {V : Type*} [Nontrivial V] {D : Digraph V}
    (hf : ∀ x y z, D x y → D x z → y = z) (hsc : StronglyConnected D) :
    ∃ C : Cycle D, C.length = Nat.card V ∧ Function.Surjective C.vertex := by
  obtain ⟨C⟩ := stronglyConnected_cycle hsc
  have hs := C.surjective_of_functional_strong hf hsc
  refine ⟨C,?_,hs⟩
  simpa only [Nat.card_fin] using Nat.card_congr (Equiv.ofBijective C.vertex ⟨C.vertex.injective,hs⟩)

end DirectedCycles
