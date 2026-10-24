import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

set_option autoImplicit false

namespace DirectedCycles

/-- A digraph without parallel arcs. Looplessness is an explicit condition. -/
abbrev Digraph (V : Type*) := V → V → Prop

def Loopless {V : Type*} (D : Digraph V) : Prop := ∀ v, ¬ D v v

def Reachable {V : Type*} (D : Digraph V) := Relation.ReflTransGen D

def StronglyConnected {V : Type*} (D : Digraph V) : Prop :=
  ∀ x y, Reachable D x y

/-- Connectedness of the underlying undirected relation, allowing zero steps. -/
def Connected {V : Type*} (D : Digraph V) : Prop :=
  ∀ x y, Relation.ReflTransGen (fun u v => D u v ∨ D v u) x y

/-- An adjacency-preserving permutation, with preservation in both directions. -/
structure Automorphism {V : Type*} (D : Digraph V) extends Equiv.Perm V where
  map_arc : ∀ x y, D (toEquiv x) (toEquiv y) ↔ D x y

def VertexTransitive {V : Type*} (D : Digraph V) : Prop :=
  ∀ x y, ∃ g : Automorphism D, g.toEquiv x = y

/-- A single simple directed cycle. `finRotate` includes the closing arc.
Length two is allowed; loops and empty cycles are excluded. -/
structure Cycle {V : Type*} (D : Digraph V) where
  length : ℕ
  two_le : 2 ≤ length
  vertex : Fin length ↪ V
  arc : ∀ i, D (vertex i) (vertex (finRotate length i))

theorem Cycle.length_le_card {V : Type*} [Fintype V] {D : Digraph V}
    (C : Cycle D) : C.length ≤ Fintype.card V := by
  simpa using Fintype.card_le_of_injective C.vertex C.vertex.injective

/-- The exact target of manuscript Theorem 1.5; a definition, not a proof.
The threshold precedes the graph order and graph. -/
def MainTheorem : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ D : Digraph (Fin n), Loopless D → Connected D → VertexTransitive D →
      ∃ C : Cycle D, (n : ℝ) ^ (1 - ε) ≤ (C.length : ℝ)

theorem stronglyConnected_connected {V : Type*} {D : Digraph V}
    (h : StronglyConnected D) : Connected D := by
  intro x y
  have hp := h x y
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp hxy ih => exact ih.tail (Or.inl hxy)

/-- Reachability maps under any arc-preserving map. -/
theorem reachable_map {V W : Type*} {D : Digraph V} {E : Digraph W}
    (f : V → W) (hf : ∀ x y, D x y → E (f x) (f y)) {x y : V}
    (h : Reachable D x y) : Reachable E (f x) (f y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h hxy ih => exact ih.tail (hf _ _ hxy)

theorem stronglyConnected_image {V W : Type*} {D : Digraph V} {E : Digraph W}
    (f : V → W) (hs : Function.Surjective f)
    (hf : ∀ x y, D x y → E (f x) (f y))
    (h : StronglyConnected D) : StronglyConnected E := by
  intro u v
  obtain ⟨x, rfl⟩ := hs u
  obtain ⟨y, rfl⟩ := hs v
  exact reachable_map f hf (h x y)

/-- An injective arc map preserves the length and simplicity of a cycle. -/
def Cycle.map {V W : Type*} {D : Digraph V} {E : Digraph W}
    (C : Cycle D) (f : V ↪ W) (hf : ∀ x y, D x y → E (f x) (f y)) : Cycle E where
  length := C.length
  two_le := C.two_le
  vertex := C.vertex.trans f
  arc i := hf _ _ (C.arc i)

theorem Automorphism.reachable_iff {V : Type*} {D : Digraph V}
    (g : Automorphism D) (x y : V) :
    Reachable D (g.toEquiv x) (g.toEquiv y) ↔ Reachable D x y := by
  constructor
  · intro h
    have hi : ∀ u v, D u v → D (g.toEquiv.symm u) (g.toEquiv.symm v) := by
      intro u v huv
      apply (g.map_arc _ _).mp
      simpa using huv
    simpa using reachable_map g.toEquiv.symm hi h
  · exact reachable_map g.toEquiv (fun u v => (g.map_arc u v).mpr)

/-- Transitivity makes all forward-reachable sets equicardinal. -/
theorem reachable_card_eq {V : Type*} [Fintype V] {D : Digraph V}
    (h : VertexTransitive D) (x y : V) :
    Set.ncard {z | Reachable D x z} = Set.ncard {z | Reachable D y z} := by
  classical
  obtain ⟨g, hg⟩ := h x y
  apply Set.ncard_congr'
  apply g.toEquiv.subtypeEquiv
  intro z
  change Reachable D x z ↔ Reachable D y (g.toEquiv z)
  rw [← hg]
  exact (g.reachable_iff x z).symm

/-- Every arc of a finite vertex-transitive digraph can be followed back by a walk. -/
theorem arc_reachable_reverse {V : Type*} [Fintype V] {D : Digraph V}
    (h : VertexTransitive D) {x y : V} (hxy : D x y) : Reachable D y x := by
  classical
  have hsub : {z | Reachable D y z} ⊆ {z | Reachable D x z} := by
    intro z hz
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hxy) hz
  have heq : {z | Reachable D y z} = {z | Reachable D x z} :=
    Set.eq_of_subset_of_ncard_le hsub (reachable_card_eq h x y).le
  have hx : x ∈ {z | Reachable D x z} := Relation.ReflTransGen.refl
  rw [← heq] at hx
  exact hx

/-- The connected/strongly-connected equivalence used throughout the manuscript.
This proof uses equal sizes of reachable sets and does not assume degree balance. -/
theorem vertexTransitive_connected_iff_stronglyConnected {V : Type*} [Fintype V]
    {D : Digraph V} (h : VertexTransitive D) :
    Connected D ↔ StronglyConnected D := by
  refine ⟨?_, stronglyConnected_connected⟩
  intro hc x y
  have hp := hc x y
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp hab ih =>
      rcases hab with hab | hba
      · exact ih.tail hab
      · exact ih.trans (arc_reachable_reverse h hba)

/-- Quotient arcs omit loops, as in the manuscript. -/
def QuotientDigraph {V W : Type*} (D : Digraph V) (π : V → W) : Digraph W :=
  fun a b => a ≠ b ∧ ∃ x y, π x = a ∧ π y = b ∧ D x y

theorem quotient_loopless {V W : Type*} (D : Digraph V) (π : V → W) :
    Loopless (QuotientDigraph D π) := fun _ h => h.1 rfl

theorem quotient_reachable {V W : Type*} (D : Digraph V) (π : V → W)
    {x y : V} (h : Reachable D x y) :
    Reachable (QuotientDigraph D π) (π x) (π y) := by
  classical
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z hp hyz ih =>
      by_cases he : π y = π z
      · simpa [← he] using ih
      · exact ih.tail ⟨he, y, z, rfl, rfl, hyz⟩

theorem quotient_stronglyConnected {V W : Type*} (D : Digraph V) (π : V → W)
    (hs : Function.Surjective π) (h : StronglyConnected D) :
    StronglyConnected (QuotientDigraph D π) := by
  intro a b
  obtain ⟨x, rfl⟩ := hs a
  obtain ⟨y, rfl⟩ := hs b
  exact quotient_reachable D π (h x y)

end DirectedCycles
