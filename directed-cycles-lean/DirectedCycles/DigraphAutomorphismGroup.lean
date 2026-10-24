import DirectedCycles.Basic

set_option autoImplicit false
namespace DirectedCycles

def automorphismGroup {V : Type*} (X : Digraph V) : Subgroup (Equiv.Perm V) where
  carrier := {g | ∀ x y, X (g x) (g y) ↔ X x y}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := by
    intro g h hg hh x y
    exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    have h := hg (g.symm x) (g.symm y)
    simpa only [Equiv.apply_symm_apply,Equiv.Perm.inv_def] using h.symm

theorem automorphismGroup_invariant {V : Type*} (X : Digraph V) :
    ∀ g : automorphismGroup X, ∀ x y, X (g • x) (g • y) ↔ X x y := fun g => g.property

theorem automorphismGroup_transitive {V : Type*} (X : Digraph V) (ht : VertexTransitive X) :
    ∀ x y : V, ∃ g : automorphismGroup X, g • x = y := by
  intro x y
  obtain ⟨g,hg⟩ := ht x y
  exact ⟨⟨g.toEquiv,g.map_arc⟩,hg⟩

theorem automorphismGroup_faithful {V : Type*} (X : Digraph V) :
    Function.Injective (MulAction.toPermHom (automorphismGroup X) V) := by
  intro g h he
  apply Subtype.ext
  exact he

end DirectedCycles
