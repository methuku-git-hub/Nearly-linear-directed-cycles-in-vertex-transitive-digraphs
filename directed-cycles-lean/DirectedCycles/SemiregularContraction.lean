import DirectedCycles.VoltageContraction
import DirectedCycles.ActionOrbitWalks

set_option autoImplicit false
universe u v
namespace DirectedCycles

/-- Manuscript Lemma 7.1. The contracted graph and its semiregular N/K
action are constructed, its orbit count is exact, and cycles lift to the
original graph through both stages without decreasing length. -/
theorem semiregular_cycle_reduction {G : Type u} {V : Type v}
    [Group G] [Finite G] [Finite V] [MulAction G V]
    (D : Digraph V) (hD : ∀ g : G, ∀ x y, D (g • x) (g • y) ↔ D x y)
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1) (hsc : StronglyConnected D)
    (a : G) (W : ActionOrbitCycleWalk G D a) (K : Subgroup G) [K.Normal]
    (haK : a ∈ K) (hproper : K ≠ ⊤) :
    ∃ (J : Type v) (_ : Finite J) (Y : Digraph ((G ⧸ K) × J)),
      letI := coordinateMulAction (G ⧸ K) J
      StronglyConnected Y ∧
      (∀ g : G ⧸ K, ∀ x y, Y (g • x) (g • y) ↔ Y x y) ∧
      (∀ g : G ⧸ K, ∀ x : (G ⧸ K) × J, g • x = x → g = 1) ∧
      Nat.card (Quotient (MulAction.orbitRel (G ⧸ K) ((G ⧸ K) × J))) =
        Nat.card (Quotient (MulAction.orbitRel G V))-W.length+1 ∧
      2 ≤ Nat.card ((G ⧸ K) × J) ∧
      (∀ C : Cycle Y, ∃ L : Cycle D, C.length ≤ L.length) := by
  let e := freeActionCoordinates hfree
  let S := orbitArcLabels hfree D
  let W' := W.toVoltageWalk hfree hD
  have hsc' := free_action_voltage_stronglyConnected hfree D hD hsc
  obtain ⟨J,hF,hJ,Y,hY,hInv,hLift⟩ := voltage_free_reduction S hsc' a W' K haK
  let : Finite J := hF
  let : MulAction (G ⧸ K) ((G ⧸ K) × J) := coordinateMulAction (G ⧸ K) J
  let : Nontrivial (G ⧸ K) := QuotientGroup.nontrivial_iff.mpr hproper
  have hJpos : 0 < Nat.card J := by rw [hJ]; omega
  have hQ2 : 2 ≤ Nat.card (G ⧸ K) := by
    let : Fintype (G ⧸ K) := Fintype.ofFinite _
    have hh := Fintype.one_lt_card (α := G ⧸ K)
    rw [Nat.card_eq_fintype_card]
    omega
  refine ⟨J,hF,Y,hY,hInv,coordinate_action_free (G ⧸ K) J,?_,?_,?_⟩
  · rw [coordinate_action_orbit_count,hJ]
    rfl
  · rw [Nat.card_prod]
    exact hQ2.trans (Nat.le_mul_of_pos_right _ hJpos)
  · intro C
    obtain ⟨L,hL⟩ := hLift C
    exact ⟨L.map e.toEmbedding (fun x y h => (free_action_voltage_arc hfree D hD x y).mp h),hL⟩

end DirectedCycles
