module

public import DirectedCycles.Paths
public import DirectedCycles.DigraphAutomorphismGroup

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

def underlyingSimpleGraph {V : Type*} (X : Digraph V) (hl : Loopless X) : SimpleGraph V where
  Adj x y := X x y ∨ X y x
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨fun x h => h.elim (hl x) (hl x)⟩

theorem underlying_preconnected {V : Type*} (X : Digraph V) (hl : Loopless X) (hc : Connected X) :
    (underlyingSimpleGraph X hl).Preconnected := by
  intro x y
  exact ((underlyingSimpleGraph X hl).reachable_iff_reflTransGen x y).mpr (hc x y)

theorem underlying_action_invariant {G V : Type*} [Group G] [MulAction G V]
    (X : Digraph V) (hl : Loopless X) (hX : ∀ g : G, ∀ x y, X (g • x) (g • y) ↔ X x y) :
    ∀ g : G, ∀ x y, (underlyingSimpleGraph X hl).Adj (g • x) (g • y) ↔
      (underlyingSimpleGraph X hl).Adj x y := by
  intro g x y
  exact or_congr (hX g x y) (hX g y x)

/-- Every vertex of a connected finite graph is reached within fewer than
its number of vertices. This justifies the full-ball growth specialization. -/
theorem connected_short_undirected_path {V : Type*} [Fintype V]
    (X : Digraph V) (hc : Connected X) (x y : V) :
    ∃ P : SimplePath (fun u v => X u v ∨ X v u) x y, P.length < Fintype.card V := by
  obtain ⟨P⟩ := simplePath_of_reachable (hc x y)
  refine ⟨P,?_⟩
  have hlen := P.nodup.length_le_card
  have hpos := List.length_pos_iff.mpr P.nonempty
  dsimp only [SimplePath.length]
  omega

end DirectedCycles
