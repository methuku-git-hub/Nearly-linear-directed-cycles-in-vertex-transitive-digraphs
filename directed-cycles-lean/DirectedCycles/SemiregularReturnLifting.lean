module

public import DirectedCycles.BasedReturnLifting
public import DirectedCycles.ActionOrbitWalks

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The auxiliary construction transfers along any injective arc map. -/
def ReturnLiftConstruction.map {G V W : Type*} [Group G] [Finite G]
    {X : Digraph V} {Y : Digraph W} {a : G} {S : Set G}
    {C : Cycle (CayleyDigraph (QuotientGroup.mk' (elementClosure a) '' S))} {r c n : ℕ}
    (R : ReturnLiftConstruction X a S C r c n) (f : V ↪ W)
    (hf : ∀ x y, X x y → Y (f x) (f y)) : ReturnLiftConstruction Y a S C r c n where
  labels := R.labels
  label_mem := R.label_mem
  step := R.step
  runs := R.runs
  bounds := R.bounds
  closing := R.closing
  endpoint := R.endpoint
  congruence := R.congruence
  nonempty := R.nonempty
  connected := R.connected
  group_le := R.group_le
  layers := R.layers
  index_bound := R.index_bound
  lift Q := by
    obtain ⟨L,hL⟩ := R.lift Q
    exact ⟨L.map f hf,hL⟩

/-- Lemma 7.2 for an arbitrary finite semiregular action. No choice of
orbit representatives, branchings, paths, or run separation is assumed. -/
theorem semiregular_return_lifting {G V : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] [Finite V] [MulAction G V]
    (X : Digraph V) (hX : ∀ g : G, ∀ x y, X (g • x) (g • y) ↔ X x y)
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1) (hsc : StronglyConnected X)
    (a : G) (W : ActionOrbitCycleWalk G X a)
    (r c n : ℕ) (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c) (hn : c ≤ n)
    (hh : 8*(Nat.card (Quotient (MulAction.orbitRel G V))+1)*((n+1)+1) <
      orderOf (QuotientGroup.mk' (elementCommutators a) a)) :
    ∃ S : Set G, (∀ s ∈ S, s ∉ elementClosure a) ∧
      StronglyConnected (CayleyDigraph (QuotientGroup.mk' (elementClosure a) '' S)) ∧
      ∀ C : Cycle (CayleyDigraph (QuotientGroup.mk' (elementClosure a) '' S)),
        Nonempty (ReturnLiftConstruction X a S C r c n) := by
  classical
  let I := Quotient (MulAction.orbitRel G V)
  let : Fintype I := Fintype.ofFinite I
  let U := orbitArcLabels hfree X
  let W' := W.toVoltageWalk hfree hX
  let p : I → G := fun _ => (W'.point 0).1
  let W'' := W'.changeRepresentatives p
  have hstart : (W''.point 0).1 = 1 := by
    change (W'.point 0).1*((W'.point 0).1)⁻¹ = 1
    exact mul_inv_cancel _
  have hsc' := free_action_voltage_stronglyConnected hfree X hX hsc
  have hh' : 8*(Fintype.card I+1)*((n+1)+1) <
      orderOf (QuotientGroup.mk' (elementCommutators a) a) := by
    simpa only [Nat.card_eq_fintype_card] using hh
  obtain ⟨S,hS,hconn,hC⟩ := based_return_lifting (gaugeLabels U p) a W'' hstart
    (gaugeLabels_stronglyConnected U p hsc') r c n hr hc hn hh'
  refine ⟨S,hS,hconn,?_⟩
  intro C
  obtain ⟨R⟩ := hC C
  let R' := R.map (gaugeCoordinates p).toEmbedding (fun x y h => (gaugeLabels_arc U p x y).mp h)
  exact ⟨R'.map (freeActionCoordinates hfree).toEmbedding
    (fun x y h => (free_action_voltage_arc hfree X hX x y).mp h)⟩

end DirectedCycles
