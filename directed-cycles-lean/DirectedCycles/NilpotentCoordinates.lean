import DirectedCycles.PowerCoordinates
import DirectedCycles.NilpotentRanks
import DirectedCycles.NilpotentOrder

set_option autoImplicit false
namespace DirectedCycles

/-- The ordered-coordinate conclusion of manuscript Lemma 3.4. -/
theorem nilpotent_power_coordinates {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (r c : ℕ) (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c) :
    ∃ k : ℕ, k ≤ (∑ i ∈ Finset.range c, r ^ (i + 1)) ∧ HasPowerCoordinates G k := by
  let k := ∑ i ∈ Finset.range c, Group.rank (LowerCentralFactor G i)
  have h := normal_series_power_coordinates (lowerSeries G)
    (fun i => Subgroup.lowerCentralSeries_antitone ⊤ (Nat.le_succ i)) c
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc)
  refine ⟨k, ?_, ?_⟩
  · apply Finset.sum_le_sum
    intro i _
    exact (lowerFactor_rank_bound G i).trans (Nat.pow_le_pow_left hr _)
  · let E : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
    exact hasPowerCoordinates_of_surjective E.toMonoidHom E.surjective h

/-- All three conclusions of manuscript Lemma 3.4: every subgroup has bounded
rank, the whole group has a fixed ordered power parametrization, and a positive
abelianization exponent bounds the group order. -/
theorem nilpotent_coordinates_bounds {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (r c : ℕ) (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c) :
    let R := ∑ i ∈ Finset.range c, r ^ (i + 1)
    (∀ U : Subgroup G, Group.rank U ≤ R) ∧
    (∃ k : ℕ, k ≤ R ∧ ∃ u : Fin k → G, ∀ g : G, ∃ t : Fin k → ℤ,
      (List.ofFn (fun i => u i ^ t i)).prod = g) ∧
    ∀ e : ℕ, 0 < e → (∀ a : Abelianization G, a ^ e = 1) → Nat.card G ≤ e ^ R := by
  refine ⟨nilpotent_subgroup_rank_bound r c hr hc, ?_, fun e he hexp => nilpotent_order_bound r c e hr hc he hexp⟩
  obtain ⟨k,hk,u,hu⟩ := nilpotent_power_coordinates r c hr hc
  exact ⟨k,hk,u,hu⟩

end DirectedCycles
