module

public import DirectedCycles.RankExtension
public import DirectedCycles.AbelianExponent
public import Mathlib.GroupTheory.Index

@[expose] public section

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- The successive factor in a normal subgroup series. -/
abbrev SeriesFactor {G : Type*} [Group G] (H : ℕ → Subgroup G) (i : ℕ) :=
  H i ⧸ (H (i + 1)).subgroupOf (H i)

/-- Ranks add along a finite descending normal series. -/
theorem rank_le_sum_series_factors {G : Type*} [Group G] [Finite G]
    (H : ℕ → Subgroup G) [∀ i, (H i).Normal] (hd : ∀ i, H (i + 1) ≤ H i)
    (c : ℕ) (h0 : H 0 = ⊤) (hc : H c = ⊥) :
    Group.rank G ≤ ∑ i ∈ Finset.range c, Group.rank (SeriesFactor H i) := by
  have hstep : ∀ i, Group.rank (H i) ≤ Group.rank (H (i + 1)) + Group.rank (SeriesFactor H i) := by
    intro i
    have h := rank_le_normal_add_quotient ((H (i + 1)).subgroupOf (H i))
    rwa [Group.rank_congr (Subgroup.subgroupOfEquivOfLe (hd i))] at h
  have hsum : ∀ n, Group.rank (H 0) ≤ Group.rank (H n) + ∑ i ∈ Finset.range n, Group.rank (SeriesFactor H i) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep n
      omega
  have h := hsum c
  rw [hc, Group.rank_eq_zero (⊥ : Subgroup G), zero_add, h0, Group.rank_congr Subgroup.topEquiv] at h
  exact h

/-- Orders multiply along a finite descending normal series. -/
theorem card_eq_prod_series_factors {G : Type*} [Group G] [Finite G]
    (H : ℕ → Subgroup G) [∀ i, (H i).Normal] (hd : ∀ i, H (i + 1) ≤ H i)
    (c : ℕ) (h0 : H 0 = ⊤) (hc : H c = ⊥) :
    Nat.card G = ∏ i ∈ Finset.range c, Nat.card (SeriesFactor H i) := by
  have hstep : ∀ i, Nat.card (H i) = Nat.card (H (i + 1)) * Nat.card (SeriesFactor H i) := by
    intro i
    have h := ((H (i + 1)).subgroupOf (H i)).card_mul_index
    rw [Subgroup.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hd i)).toEquiv] at h
    exact h.symm
  have hprod : ∀ n, Nat.card (H 0) = Nat.card (H n) * ∏ i ∈ Finset.range n, Nat.card (SeriesFactor H i) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, ih, hstep n]
      ring
  have h := hprod c
  simpa only [h0, hc, Subgroup.card_top, Subgroup.card_bot, one_mul] using h

/-- The numerical order bound once ranks and exponents of the abelian
factors of the series have been established. -/
theorem card_le_exponent_pow_sum_factor_ranks {G : Type*} [Group G] [Fintype G]
    (H : ℕ → Subgroup G) [∀ i, (H i).Normal] (hd : ∀ i, H (i + 1) ≤ H i)
    (c e : ℕ) (he : 0 < e) (h0 : H 0 = ⊤) (hc : H c = ⊥)
    [∀ i, IsMulCommutative (SeriesFactor H i)]
    (a : ℕ → ℕ) (hrank : ∀ i < c, Group.rank (SeriesFactor H i) ≤ a i)
    (hexp : ∀ i < c, ∀ x : SeriesFactor H i, x ^ e = 1) :
    Nat.card G ≤ e ^ (∑ i ∈ Finset.range c, a i) := by
  rw [card_eq_prod_series_factors H hd c h0 hc]
  calc (∏ i ∈ Finset.range c, Nat.card (SeriesFactor H i)) ≤ ∏ i ∈ Finset.range c, e ^ a i := by
         apply Finset.prod_le_prod
         intro i hi
         have hic : i < c := Finset.mem_range.mp hi
         let : Fintype (SeriesFactor H i) := Fintype.ofFinite _
         let : CommGroup (SeriesFactor H i) := { (inferInstance : Group (SeriesFactor H i)) with mul_comm := mul_comm' }
         have h := finite_abelian_card_le_exponent_rank e he (hexp i hic)
         have hcard : Nat.card (SeriesFactor H i) ≤ e ^ Group.rank (SeriesFactor H i) := by
           simpa only [Nat.card_eq_fintype_card] using h
         exact hcard.trans (Nat.pow_le_pow_right (by omega) (hrank i hic))
       _ = e ^ (∑ i ∈ Finset.range c, a i) := Finset.prod_pow_eq_pow_sum _ _ _

end DirectedCycles
