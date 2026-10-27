module

public import DirectedCycles.JoiningConnections
public import DirectedCycles.SingleOrbitPaths

@[expose] public section

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- A single loop in the auxiliary connection graph suffices when every
ordered pair of vertices has a short directed route. -/
theorem cycle_of_uniform_short_paths {G V : Type*} [Group G] [Fintype G]
    [Fintype V] [MulAction G V] (D : Digraph V)
    (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (t : ℕ)
    (hshort : ∀ x y, ∃ P : SimplePath D x y, P.length ≤ t)
    (hlarge : 192 * (t + 1) ^ 2 ≤ Fintype.card V) :
    ∃ C : Cycle D, (Fintype.card V : ℝ) / (96 * (t + 1 : ℝ) ^ 2) ≤ C.length := by
  let Q : Digraph Unit := fun _ _ => True
  let π : V → Unit := fun _ => ()
  have hn : 0 < Fintype.card V := lt_of_lt_of_le (by positivity : 0 < 192 * (t + 1) ^ 2) hlarge
  obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp hn
  have hs : Function.Surjective π := fun a => ⟨x₀, Subsingleton.elim _ _⟩
  have hQi : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b := fun _ _ _ => Iff.rfl
  have hπ : ∀ (g : G) x, π (g • x) = g • π x := fun _ _ => Subsingleton.elim _ _
  have hQ : StronglyConnected Q := fun _ _ => Relation.ReflTransGen.single trivial
  have hm : ∀ a, Fintype.card {x // π x = a} = Fintype.card V := by
    intro a
    have hπa : ∀ x, π x = a := fun _ => Subsingleton.elim _ _
    simp only [Fintype.card_subtype, hπa, Finset.filter_true, Finset.card_univ]
  apply joining_short_connections_on_partition D Q π hs hD hQi hπ ht hQ
    (by decide) (Fintype.card V) 1 t (by decide) hm
  · intro a; simp [Q]
  · intro a; simp [Q]
  · intro a b _ x y
    exact hshort x.val y.val
  · simpa using hlarge

/-- The single-normal-orbit case is obtained from the same route sampler as
the multiple-orbit case, with no external expansion-to-cycle theorem. -/
theorem single_orbit_sampling_bound {G V : Type*} [Group G] [Fintype G]
    [Fintype V] [DecidableEq V] [MulAction G V] (H : Subgroup G) [H.Normal]
    [Fintype (Quotient (MulAction.orbitRel H V))]
    [DecidableEq (Quotient (MulAction.orbitRel H V))]
    (D : Digraph V) (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (hn : 2 ≤ Fintype.card V)
    (hq : Fintype.card (Quotient (MulAction.orbitRel H V)) = 1)
    (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hdiam : ∀ x y, MulAction.orbitRel H V x y →
      ∃ P : SimplePath (fun u v => D u v ∨ D v u) x y, (P.length : ℝ) ≤ ρ)
    (hlarge : 192 * (2 * ⌈4 * ρ * Real.log (2 * (Fintype.card V : ℝ))⌉₊ + 2) ^ 2 ≤ Fintype.card V) :
    ∃ C : Cycle D, (Fintype.card V : ℝ) /
      (96 * (2 * (⌈4 * ρ * Real.log (2 * (Fintype.card V : ℝ))⌉₊ : ℝ) + 2) ^ 2) ≤ C.length := by
  let u := ⌈4 * ρ * Real.log (2 * (Fintype.card V : ℝ))⌉₊
  have hshort : ∀ x y, ∃ P : SimplePath D x y, P.length ≤ 2 * u + 1 := by
    intro x y
    obtain ⟨P, hP⟩ := single_orbit_short_paths H D hD ht hn hq ρ hρ hdiam x y
    exact ⟨P, by omega⟩
  obtain ⟨C, hC⟩ := cycle_of_uniform_short_paths D hD ht (2 * u + 1) hshort (by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hlarge)
  refine ⟨C, ?_⟩
  convert hC using 1
  push_cast
  ring

end DirectedCycles
