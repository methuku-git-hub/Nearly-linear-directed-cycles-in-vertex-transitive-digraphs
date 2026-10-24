import DirectedCycles.LowerCentralFactors
import DirectedCycles.SubgroupSeries

set_option autoImplicit false
namespace DirectedCycles

/-- The subgroup generator conclusion of manuscript Lemma 3.4. -/
theorem nilpotent_subgroup_rank_bound {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (r c : ℕ) (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c) (U : Subgroup G) :
    Group.rank U ≤ ∑ i ∈ Finset.range c, r ^ (i + 1) := by
  apply (subgroup_rank_le_sum_series_factors (lowerSeries G)
    (fun i => Subgroup.lowerCentralSeries_antitone ⊤ (Nat.le_succ i)) c rfl
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc) U).trans
  apply Finset.sum_le_sum
  intro i _
  exact (lowerFactor_rank_bound G i).trans (Nat.pow_le_pow_left hr _)

end DirectedCycles
