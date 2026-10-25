module

public import DirectedCycles.OrbitWalkHamiltonian
public import DirectedCycles.OrbitCycleLifting
public import DirectedCycles.ActionOrbitWalks
public import DirectedCycles.OrbitWalkPaths
public import DirectedCycles.StrongCycleExistence

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

theorem finite_nontrivial_of_two_le_card {V : Type*} [Finite V]
    (h : 2 ≤ Nat.card V) : Nontrivial V := by
  let : Fintype V := Fintype.ofFinite V
  apply Fintype.one_lt_card_iff_nontrivial.mp
  rw [← Nat.card_eq_fintype_card]
  omega

/-- A semiregular action with at least two orbits admits an actual lifted
simple orbit cycle, with its endpoint group element. -/
theorem semiregular_orbit_cycle_walk {G V : Type*} [Group G] [MulAction G V] [Finite V]
    (X : Digraph V) (hX : ∀ g : G, ∀ x y, X (g • x) (g • y) ↔ X x y)
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1) (hsc : StronglyConnected X)
    (hq : 2 ≤ Nat.card (Quotient (MulAction.orbitRel G V))) :
    ∃ a : G, Nonempty (ActionOrbitCycleWalk G X a) := by
  let I := Quotient (MulAction.orbitRel G V)
  let : Nontrivial I := finite_nontrivial_of_two_le_card hq
  let U := orbitArcLabels hfree X
  have hU := free_action_voltage_stronglyConnected hfree X hX hsc
  have hQ := quotient_stronglyConnected (VoltageDigraph U) Prod.snd (fun i => ⟨(1,i),rfl⟩) hU
  obtain ⟨Q⟩ := stronglyConnected_cycle hQ
  obtain ⟨a,W,_hL,_hstart⟩ := voltage_orbit_cycle_walk U Q
  refine ⟨a,⟨{
    length := W.length
    two_le := W.two_le
    point := fun i => freeActionCoordinates hfree (W.point i)
    index_injective := ?_
    step := ?_
    closes := ?_
  }⟩⟩
  · intro i j he
    simp only [freeActionCoordinates_orbit] at he
    exact W.index_injective he
  · intro i
    exact (free_action_voltage_arc hfree X hX _ _).mp (W.step i)
  · rw [W.closes,freeActionCoordinates_smul]

/-- The cyclic branch of Theorem 3.7, including trivial groups: a generating
orbit voltage covers all vertices of the selected orbits. -/
theorem semiregular_generating_voltage_cycle {G V : Type*} [Group G] [Finite G] [MulAction G V]
    (X : Digraph V) (hX : ∀ g : G, ∀ x y, X (g • x) (g • y) ↔ X x y)
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1)
    (a : G) (W : ActionOrbitCycleWalk G X a) (hgen : Subgroup.zpowers a = ⊤) :
    ∃ C : Cycle X, C.length = W.length*Nat.card G := by
  let U := orbitArcLabels hfree X
  let W' := W.toVoltageWalk hfree hX
  let p := fun _ : Quotient (MulAction.orbitRel G V) => (W'.point 0).1
  let W'' := W'.changeRepresentatives p
  have hstart : (W''.point 0).1 = 1 := mul_inv_cancel _
  obtain ⟨L,hL⟩ := W''.generating_voltage_cycle hstart hgen
  let L' := L.map (gaugeCoordinates p).toEmbedding (fun x y h => (gaugeLabels_arc U p x y).mp h)
  exact ⟨L'.map (freeActionCoordinates hfree).toEmbedding
    (fun x y h => (free_action_voltage_arc hfree X hX x y).mp h),hL⟩

/-- With exactly one free orbit, the graph is an actual Cayley digraph. -/
theorem one_orbit_cayley_presentation {G V : Type*} [Group G] [MulAction G V]
    (X : Digraph V) (hX : ∀ g : G, ∀ x y, X (g • x) (g • y) ↔ X x y)
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1) (hsc : StronglyConnected X)
    (hq : Nat.card (Quotient (MulAction.orbitRel G V)) = 1) :
    ∃ S : Set G, StronglyConnected (CayleyDigraph S) ∧
      ∃ f : G ↪ V, ∀ x y, CayleyDigraph S x y → X (f x) (f y) := by
  let I := Quotient (MulAction.orbitRel G V)
  obtain ⟨i,hi⟩ := Nat.card_eq_one_iff_exists.mp hq
  let U := orbitArcLabels hfree X
  let S := U i i
  let f : G ↪ V := (⟨fun g => (g,i),fun _ _ he => congrArg Prod.fst he⟩ : G ↪ G × I).trans
    (freeActionCoordinates hfree).toEmbedding
  refine ⟨S,?_,f,?_⟩
  · apply stronglyConnected_image Prod.fst (fun g => ⟨(g,i),rfl⟩) _
      (free_action_voltage_stronglyConnected hfree X hX hsc)
    rintro x y ⟨s,hs,he⟩
    exact ⟨s,by simpa only [hi x.2,hi y.2] using hs,he⟩
  · rintro x y ⟨s,hs,he⟩
    exact (free_action_voltage_arc hfree X hX (x,i) (y,i)).mp ⟨s,hs,he⟩

end DirectedCycles
