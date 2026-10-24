import DirectedCycles.AbelianLayerBounds
import DirectedCycles.LayerEquivalence

set_option autoImplicit false
namespace DirectedCycles

/-- The fixed cutoff used for the integral spanning invariant. -/
def AbovePrimeCutoff (G : Type*) (D : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ Nat.card G → 8*D+4 < p

/-- The Cayley conclusion together with the large-prime invariant. -/
def CayleySpanningBound (G : Type*) [Group G] (D : ℕ) (b eta : ℝ) : Prop :=
  Nontrivial G → ∀ S : Set G, Subgroup.closure S = ⊤ →
    ∃ C : Cycle (CayleyDigraph S), b*(Nat.card G : ℝ)^(1-eta) ≤ C.length ∧
      (AbovePrimeCutoff G D → SpansTruncation D (Set.range C.vertex))

/-- The cyclic-layer conclusion needed by the simultaneous induction. The
single-layer case is handled by the Cayley conclusion; the singleton loop
convention is therefore absent here. -/
def LayerSpanningBound (G : Type*) [Group G] (D : ℕ) (b eta : ℝ) : Prop :=
  ∀ T : ℕ, 2 ≤ T → ∀ S : ZMod T → Set G, (∀ z, (S z).Nonempty) →
    StronglyConnected (CyclicLayerDigraph S) →
    ∃ C : Cycle (CyclicLayerDigraph S), b*T*(Nat.card G : ℝ)^(1-eta) ≤ C.length ∧
      (AbovePrimeCutoff G D → ∀ z, SpansTruncation D (C.layerCoordinates z))

theorem LayerSpanningBound.to_lower_bound {G : Type*} [Group G] {D : ℕ} {b eta : ℝ}
    (h : LayerSpanningBound G D b eta) : LayerCycleLowerBound G b eta := by
  intro T hT S hS hsc
  obtain ⟨C,hC,_⟩ := h T hT S hS hsc
  exact ⟨C,hC⟩

theorem cardinal_rpow_le_card {G : Type*} [Group G] [Finite G]
    (eta : ℝ) (heta : 0 ≤ eta) : (Nat.card G : ℝ)^(1-eta) ≤ Nat.card G := by
  have hcard : (1 : ℝ) ≤ Nat.card G := by exact_mod_cast (Nat.card_pos (α := G))
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hcard (show 1-eta ≤ 1 by linarith)

/-- Both strengthened abelian base cases with a common explicit constant. -/
theorem abelian_spanning_bounds {G : Type*} [CommGroup G] [Finite G]
    (r D : ℕ) (hr : Group.rank G ≤ r) (eta : ℝ) (heta : 0 ≤ eta) :
    CayleySpanningBound G D (abelianLayerConstant r D) eta ∧
      LayerSpanningBound G D (abelianLayerConstant r D) eta := by
  obtain ⟨hb,hb8,_⟩ := abelianLayerConstant_bounds r D
  have hpow := cardinal_rpow_le_card (G := G) eta heta
  constructor
  · intro hnt S hS
    let : Nontrivial G := hnt
    obtain ⟨C,hC,hspan⟩ := abelian_cayley_cycle S hS
    refine ⟨C,?_,?_⟩
    · have hscale := mul_le_mul_of_nonneg_left hpow hb.le
      have hhalf : abelianLayerConstant r D ≤ 1/2 := by linarith
      have hsmall := mul_le_mul_of_nonneg_right hhalf (by positivity : (0 : ℝ) ≤ Nat.card G)
      nlinarith
    · intro hp
      apply (hspan D hp).mono
      intro x hx
      exact List.mem_ofFn.mp ((List.dropLast_sublist _).subset hx)
  · intro T hT S _ hsc
    obtain ⟨C,hC,hspan⟩ := abelian_layer_cycle_bound r D hr hT S hsc
    refine ⟨C,?_,hspan⟩
    exact (mul_le_mul_of_nonneg_left hpow (mul_nonneg hb.le (Nat.cast_nonneg T))).trans hC

end DirectedCycles
