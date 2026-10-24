import DirectedCycles.OrbitCycleWalk
import DirectedCycles.CoordinateActions

set_option autoImplicit false
universe u v
namespace DirectedCycles

/-- The directed contraction step in group coordinates. The resulting graph
has a free quotient-group action, the exact reduced orbit count, and cycle
lifts through both the contracted cycles and the normal-subgroup fibres. -/
theorem voltage_free_reduction {G : Type u} {I : Type v} [Group G] [Finite G] [Finite I]
    (S : I → I → Set G) (hsc : StronglyConnected (VoltageDigraph S))
    (a : G) (W : OrbitCycleWalk (VoltageDigraph S) a)
    (K : Subgroup G) [K.Normal] (haK : a ∈ K) :
    ∃ (J : Type v) (_ : Finite J), Nat.card J = Nat.card I-W.length+1 ∧
      ∃ Y : Digraph ((G ⧸ K) × J), StronglyConnected Y ∧
        (∀ g : G ⧸ K, ∀ x y, Y (g*x.1,x.2) (g*y.1,y.2) ↔ Y x y) ∧
        (∀ C : Cycle Y, ∃ L : Cycle (VoltageDigraph S), C.length ≤ L.length) := by
  let q := QuotientGroup.mk' K
  have hqa : q a = 1 := (QuotientGroup.eq_one_iff a).mpr haK
  let C := W.quotientCycle q hqa
  have hC := W.quotientCycle_indices_injective q hqa
  let J := Option C.UnusedIndices
  let Y := QuotientDigraph (VoltageDigraph (fun i j => q '' S i j)) C.contractProjection
  have hscQ := voltage_quotient_stronglyConnected q (QuotientGroup.mk'_surjective K) S hsc
  have hleft := voltage_left_invariant (fun i j => q '' S i j)
  obtain ⟨hscY,hlift⟩ := C.contraction_connectivity_and_lifting hC hleft hscQ
  refine ⟨J,inferInstance,C.contraction_orbit_count hC,Y,hscY,C.contracted_graph_left_invariant hleft,?_⟩
  intro L
  obtain ⟨Q,hQ⟩ := hlift L
  obtain ⟨R,hR⟩ := voltage_quotient_cycle_lift q (QuotientGroup.mk'_surjective K) S Q
  exact ⟨R,hQ.trans hR⟩

end DirectedCycles
