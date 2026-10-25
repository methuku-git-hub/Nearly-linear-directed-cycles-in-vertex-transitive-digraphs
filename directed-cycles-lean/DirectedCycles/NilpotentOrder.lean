module

public import DirectedCycles.LowerCentralFactors

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The order conclusion of manuscript Lemma 3.4. Positivity of the exponent
parameter is explicit; in stabilizer removal it is the order of a subgroup. -/
theorem nilpotent_order_bound {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (r c e : ℕ) (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c)
    (he : 0 < e) (hexp : ∀ a : Abelianization G, a ^ e = 1) :
    Nat.card G ≤ e ^ (∑ i ∈ Finset.range c, r ^ (i + 1)) := by
  let : Fintype G := Fintype.ofFinite G
  apply card_le_exponent_pow_sum_factor_ranks (lowerSeries G)
    (fun i => Subgroup.lowerCentralSeries_antitone ⊤ (Nat.le_succ i)) c e he rfl
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc) (fun i => r ^ (i + 1))
  · intro i _
    exact (lowerFactor_rank_bound G i).trans (Nat.pow_le_pow_left hr _)
  · intro i _
    exact lowerFactor_exponent G e hexp i

end DirectedCycles
