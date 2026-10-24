import DirectedCycles.SubgroupIndexFactors

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- Power coverage in the abelianization bounds the index of any subgroup.
The subgroup is not assumed normal. -/
theorem nilpotent_subgroup_index_of_power_coverage {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] (C : Subgroup G) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ x : G, x^m ∈ C ⊔ commutator G) (r c : ℕ)
    (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c) :
    C.index ≤ m^(∑ i ∈ Finset.range c, (i+1)*r^(i+1)) := by
  let J : ℕ → Subgroup C := fun i => (lowerSeries G i).subgroupOf C
  have hbot : lowerSeries G c = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc
  have hG := card_eq_prod_series_factors (lowerSeries G)
    (fun i => Subgroup.lowerCentralSeries_antitone ⊤ (Nat.le_succ i)) c rfl hbot
  have hC := card_eq_prod_series_factors J
    (fun i => Subgroup.subgroupOf_mono C
      (Subgroup.lowerCentralSeries_antitone ⊤ (Nat.le_succ i))) c
    (by simp [J,lowerSeries]) (by simp [J,hbot])
  have horder : Nat.card G ≤ Nat.card C * m^(∑ i ∈ Finset.range c, (i+1)*r^(i+1)) := by
    rw [hG,hC,← Finset.prod_pow_eq_pow_sum,← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    intro i _
    exact lowerFactor_card_le_intersected_factor C m hm hbase i r hr
  rw [← C.card_mul_index] at horder
  exact (Nat.mul_le_mul_left_iff (Nat.card_pos (α := C))).mp horder

/-- The exact abelianization form used by the auxiliary-group index proof. -/
theorem nilpotent_subgroup_index_of_abelian_power {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] (C : Subgroup G) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ x : Abelianization G, x^m ∈ C.map ((Abelianization.of : G →* Abelianization G)))
    (r c : ℕ) (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c) :
    C.index ≤ m^(∑ i ∈ Finset.range c, (i+1)*r^(i+1)) := by
  apply nilpotent_subgroup_index_of_power_coverage C m hm _ r c hr hc
  intro x
  have h : x^m ∈ (C.map ((Abelianization.of : G →* Abelianization G))).comap ((Abelianization.of : G →* Abelianization G)) := by
    change Abelianization.of (x^m) ∈ C.map (Abelianization.of : G →* Abelianization G)
    rw [map_pow]
    exact hbase _
  simpa only [Subgroup.comap_map_eq,Abelianization.ker_of] using h

end DirectedCycles
