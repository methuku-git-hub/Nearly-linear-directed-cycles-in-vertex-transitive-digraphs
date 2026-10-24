import DirectedCycles.LowerCentralFactors

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- The three-subgroup lemma modulo an arbitrary normal subgroup. -/
theorem commutator_commutator_le_of_rotate {G : Type*} [Group G]
    (A B C N : Subgroup G) [N.Normal]
    (h₁ : ⁅⁅B,C⁆,A⁆ ≤ N) (h₂ : ⁅⁅C,A⁆,B⁆ ≤ N) : ⁅⁅A,B⁆,C⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  have hm (H : Subgroup G) : H.map q = ⊥ ↔ H ≤ N := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  apply (hm _).mp
  rw [Subgroup.map_commutator, Subgroup.map_commutator]
  apply Subgroup.commutator_commutator_eq_bot_of_rotate
  · simpa only [Subgroup.map_commutator] using (hm _).mpr h₁
  · simpa only [Subgroup.map_commutator] using (hm _).mpr h₂

/-- Commutator weights add in the lower central series. Its index zero is G. -/
theorem lowerSeries_commutator_le {G : Type*} [Group G] (i j : ℕ) :
    ⁅lowerSeries G i, lowerSeries G j⁆ ≤ lowerSeries G (i+j+1) := by
  induction i generalizing j with
  | zero =>
    rw [Subgroup.commutator_comm]
    simp only [Nat.zero_add, lowerSeries, Subgroup.lowerCentralSeries_zero,
      Subgroup.lowerCentralSeries_succ]
    exact le_rfl
  | succ i ih =>
    change ⁅⁅lowerSeries G i, (⊤ : Subgroup G)⁆, lowerSeries G j⁆ ≤ _
    apply commutator_commutator_le_of_rotate
    · rw [Subgroup.commutator_comm (⊤ : Subgroup G),
        Subgroup.commutator_comm (⁅lowerSeries G j, (⊤ : Subgroup G)⁆)]
      have hh := ih (j+1)
      rw [show i+(j+1)+1 = i+1+j+1 by omega] at hh
      exact hh
    · have h : ⁅lowerSeries G j, lowerSeries G i⁆ ≤ lowerSeries G (i+j+1) := by
        rw [Subgroup.commutator_comm]
        exact ih j
      have hh := Subgroup.commutator_mono h (le_refl (⊤ : Subgroup G))
      change ⁅⁅lowerSeries G j, lowerSeries G i⁆, (⊤ : Subgroup G)⁆ ≤ lowerSeries G ((i+j+1)+1) at hh
      convert hh using 1
      congr 1
      omega

/-- The j-th lower central term of a subgroup of G' has ambient weight at
least 2(j+1). -/
theorem commutator_subgroup_lowerSeries_le {G : Type*} [Group G] (H : Subgroup G)
    (hH : H ≤ commutator G) (j : ℕ) :
    H.lowerCentralSeries j ≤ lowerSeries G (2*j+1) := by
  induction j with
  | zero =>
    simpa only [Nat.mul_zero, Nat.zero_add, Subgroup.lowerCentralSeries_zero,
      lowerSeries, Subgroup.top_lowerCentralSeries_one] using hH
  | succ j ih =>
    have h := (Subgroup.commutator_mono ih hH).trans (lowerSeries_commutator_le (2*j+1) 1)
    simpa only [Subgroup.lowerCentralSeries_succ, Nat.mul_add, Nat.mul_one,
      Nat.add_assoc] using h

/-- Passing to a subgroup of the derived group halves a finite nilpotency
class bound, as needed for the induction in the directed-lifting theorem. -/
theorem commutator_subgroup_class_le_half {G : Type*} [Group G] [Group.IsNilpotent G]
    (H : Subgroup G) (hH : H ≤ commutator G) (c : ℕ)
    (hc : Group.nilpotencyClass G ≤ c) : Group.nilpotencyClass H ≤ c/2 := by
  apply Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
  apply (Subgroup.map_injective H.subtype_injective).eq_iff.mp
  rw [Subgroup.map_bot, Subgroup.top_subtype_lowerCentralSeries]
  apply le_antisymm _ bot_le
  calc H.lowerCentralSeries (c/2) ≤ lowerSeries G (2*(c/2)+1) :=
        commutator_subgroup_lowerSeries_le H hH _
       _ ≤ lowerSeries G c := Subgroup.lowerCentralSeries_antitone ⊤ (by omega)
       _ = ⊥ := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc

end DirectedCycles
