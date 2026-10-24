import DirectedCycles.PrimeBudget
import DirectedCycles.CyclicGeneratorCycle
import DirectedCycles.CayleyQuotientLift
import DirectedCycles.DirectedLifting
import DirectedCycles.BudgetConstants
import DirectedCycles.LowerClassInputs
import DirectedCycles.NilpotentCycleBounds

set_option autoImplicit false
universe u
namespace DirectedCycles

/-- Reconstructing through the bounded number of small-prime steps. All
constants and exponent changes are independent of the label set and group. -/
theorem bounded_prime_cayley_density (r c n : ℕ) (hcn : c ≤ n)
    (base lower theta : ℝ) (hb : 0 < base) (hb1 : base ≤ 1)
    (hl : 0 < lower) (htheta : 0 ≤ theta)
    (hbase : ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H],
      Group.rank H ≤ r → Group.nilpotencyClass H ≤ c → AbovePrimeCutoff H (n+1) →
      CayleySpanningBound H (n+1) base theta)
    (hlower : ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H],
      Group.rank H ≤ ∑ i ∈ Finset.range c, r^(i+1) →
      Group.nilpotencyClass H ≤ c/2 → LayerCycleLowerBound H lower theta)
    (t : ℕ) (G : Type u) [Group G] [Finite G] [Group.IsNilpotent G] [Nontrivial G]
    (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c)
    (hbudget : primeBudget G (8*(n+1)+4) ≤ t) (S : Set G) (hS : Subgroup.closure S = ⊤) :
    let k := auxiliaryIndexExponent r c n+1
    let d := lower/(4*(auxiliaryIndexConstant r c n : ℝ))
    let M : ℝ := ((8*(n+1)+4)^(c*∑ i ∈ Finset.range c, r^(i+1)) : ℕ)
    ∃ C : Cycle (CayleyDigraph S), budgetConstant base d M k t*
      (Nat.card G : ℝ)^(-(theta*(k : ℝ)^t)) ≤ (C.length : ℝ)/Nat.card G := by
  let k := auxiliaryIndexExponent r c n+1
  let d := lower/(4*(auxiliaryIndexConstant r c n : ℝ))
  let Mnat := (8*(n+1)+4)^(c*∑ i ∈ Finset.range c, r^(i+1))
  let M : ℝ := Mnat
  have hk : 1 ≤ k := by dsimp only [k]; omega
  have hd : 0 < d := by
    have hJ : (0 : ℝ) < auxiliaryIndexConstant r c n := by exact_mod_cast auxiliaryIndexConstant_pos r c n
    exact div_pos hl (mul_pos (by norm_num) hJ)
  have hM : 1 ≤ M := by
    change (1 : ℝ) ≤ (Mnat : ℝ)
    have hmnat : 1 ≤ Mnat := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    exact_mod_cast hmnat
  have hstart : ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H] [Nontrivial H],
      Group.rank H ≤ r → Group.nilpotencyClass H ≤ c → AbovePrimeCutoff H (n+1) →
      ∀ t : ℕ, ∀ A : Set H, Subgroup.closure A = ⊤ →
      ∃ C : Cycle (CayleyDigraph A), budgetConstant base d M k t*
        (Nat.card H : ℝ)^(-(theta*(k : ℝ)^t)) ≤ (C.length : ℝ)/Nat.card H := by
    intro H _ _ _ _ hrH hcH hpH t A hA
    obtain ⟨C,hC,_⟩ := hbase H hrH hcH hpH inferInstance A hA
    have hNpos : (0 : ℝ) < Nat.card H := by exact_mod_cast (Nat.card_pos (α := H))
    have hN1 : (1 : ℝ) ≤ Nat.card H := by exact_mod_cast (Nat.card_pos (α := H))
    have hdensity := (length_bound_iff_density_bound base (Nat.card H) theta C.length hNpos).mp hC
    exact ⟨C,density_bound_weaken base _ theta _ (Nat.card H) _ hb.le
      (budgetConstant_le_base base d M k t hb hd hM) (budget_error_step theta k t htheta hk).1 hN1 hdensity⟩
  have hall : ∀ t : ℕ, ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H] [Nontrivial H],
      Group.rank H ≤ r → Group.nilpotencyClass H ≤ c → primeBudget H (8*(n+1)+4) ≤ t →
      ∀ A : Set H, Subgroup.closure A = ⊤ →
      ∃ C : Cycle (CayleyDigraph A), budgetConstant base d M k t*
        (Nat.card H : ℝ)^(-(theta*(k : ℝ)^t)) ≤ (C.length : ℝ)/Nat.card H := by
    intro t
    induction t with
    | zero =>
      intro H _ _ _ _ hrH hcH hbud A hA
      have hpH : AbovePrimeCutoff H (n+1) := no_small_primes_of_zero_budget _ (by omega)
      exact hstart H hrH hcH hpH 0 A hA
    | succ t ih =>
      intro H _ _ _ _ hrH hcH hbud A hA
      by_cases hpH : AbovePrimeCutoff H (n+1)
      · exact hstart H hrH hcH hpH (t+1) A hA
      · change ¬ ∀ p : ℕ, p.Prime → p ∣ Nat.card H → 8*(n+1)+4 < p at hpH
        push Not at hpH
        obtain ⟨p,hprime,hpd,hsmall⟩ := hpH
        let : Fact p.Prime := ⟨hprime⟩
        obtain ⟨a,haA,_,hdrop,_,hcyclic⟩ := nilpotent_prime_quotient_step A hA p hpd
        by_cases htop : elementClosure a = ⊤
        · obtain ⟨C,hC,_⟩ := cyclic_generator_cycle A a haA (hcyclic htop)
          refine ⟨C,?_⟩
          have hNpos : (0 : ℝ) < Nat.card H := by exact_mod_cast (Nat.card_pos (α := H))
          have hN1 : (1 : ℝ) ≤ Nat.card H := by exact_mod_cast (Nat.card_pos (α := H))
          rw [hC,div_self hNpos.ne']
          have hconst := (budgetConstant_le_base base d M k (t+1) hb hd hM).trans hb1
          have hpow := Real.rpow_le_one_of_one_le_of_nonpos hN1
            (neg_nonpos.mpr (mul_nonneg htheta (pow_nonneg (Nat.cast_nonneg k) (t+1))))
          exact (mul_le_mul hconst hpow (Real.rpow_nonneg hNpos.le _) zero_le_one).trans_eq (one_mul 1)
        · let K := elementClosure a
          let B := elementCommutators a
          let q := QuotientGroup.mk' K
          let : Nontrivial (H ⧸ K) := QuotientGroup.nontrivial_iff.mpr htop
          have hrQ : Group.rank (H ⧸ K) ≤ r :=
            (Group.rank_le_of_surjective q (QuotientGroup.mk'_surjective K)).trans hrH
          have hcQ : Group.nilpotencyClass (H ⧸ K) ≤ c := (Group.nilpotencyClass_quotient_le K).trans hcH
          have hbudQ : primeBudget (H ⧸ K) (8*(n+1)+4) ≤ t := by
            have hh := primeBudget_drop p (8*(n+1)+4) hsmall a hdrop
            change primeBudget (H ⧸ elementClosure a) (8*(n+1)+4) ≤ t
            omega
          have hqA : Subgroup.closure (q '' A) = ⊤ := by
            rw [← MonoidHom.map_closure,hA,Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
          obtain ⟨Q,hQ⟩ := ih (H ⧸ K) hrQ hcQ hbudQ (q '' A) hqA
          let beta := theta*(k : ℝ)^t
          have hbeta : 0 ≤ beta := mul_nonneg htheta (pow_nonneg (Nat.cast_nonneg _) _)
          have hqpos : (0 : ℝ) < Nat.card (H ⧸ K) := by exact_mod_cast (Nat.card_pos (α := H ⧸ K))
          have hK1 : (1 : ℝ) ≤ Nat.card K := by exact_mod_cast (Nat.card_pos (α := K))
          have hN1 : (1 : ℝ) ≤ Nat.card H := by exact_mod_cast (Nat.card_pos (α := H))
          have hbct := budgetConstant_pos base d M k t hb hd (zero_lt_one.trans_le hM)
          have herror := budget_error_step theta k t htheta hk
          let h := Nat.card (K ⧸ B.subgroupOf K)
          by_cases hh : h ≤ 8*(n+1)+4
          · have hKM : (Nat.card K : ℝ) ≤ M := by
              have hbound := elementClosure_order_bound a r c hrH hcH
              have hpw := Nat.pow_le_pow_left hh (c*∑ i ∈ Finset.range c,r^(i+1))
              dsimp only [K,M,Mnat]
              exact_mod_cast hbound.trans hpw
            obtain ⟨C,hC⟩ := cayley_quotient_cycle_lift q (QuotientGroup.mk'_surjective K) A Q
            have hid : (Nat.card H : ℝ) = (Nat.card (H ⧸ K) : ℝ)*Nat.card K := by
              exact_mod_cast K.card_eq_card_quotient_mul_card_subgroup
            have hcalc := small_kernel_density (budgetConstant base d M k t) (Nat.card (H ⧸ K))
              (Nat.card K) M (Nat.card H) beta Q.length C.length hbct.le hqpos hK1 hKM hid hbeta hQ
              (by exact_mod_cast hC)
            exact ⟨C,density_bound_weaken _ _ beta _ (Nat.card H) _ (div_nonneg hbct.le (zero_le_one.trans hM))
              (min_le_left _ _) herror.2.1 hN1 hcalc⟩
          · have hlayers : ∀ U : Subgroup B, LayerCycleLowerBound U lower theta := by
              intro U
              obtain ⟨hrU,hcU⟩ := elementCommutators_subgroup_bounds a r c hrH hcH U
              exact hlower U hrU hcU
            obtain ⟨C,_,hC⟩ := directed_cycle_lifting a A haA r c n hrH hcH hcn
              (show 8*(n+1)+4 < h from by omega)
              Q lower theta hl htheta hlayers
            have hid : (Nat.card H : ℝ) = (Nat.card (H ⧸ K) : ℝ)*h*Nat.card B := by
              exact_mod_cast elementClosure_card_factorization a
            have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (Nat.card_pos (α := K ⧸ B.subgroupOf K))
            have hB1 : (1 : ℝ) ≤ Nat.card B := by exact_mod_cast (Nat.card_pos (α := B))
            have hthetabeta : theta ≤ (k : ℝ)*beta := by
              rw [← herror.2.2]
              exact herror.1.trans herror.2.1
            have hcalc := large_kernel_density (budgetConstant base d M k t) d (Nat.card (H ⧸ K)) h
              (Nat.card B) (Nat.card H) beta theta Q.length ((C.length : ℝ)/Nat.card H) k
              hbct.le hd.le hqpos hh1 hB1 hid htheta hthetabeta hQ hC
            rw [← herror.2.2] at hcalc
            exact ⟨C,(mul_le_mul_of_nonneg_right (min_le_right _ _)
              (Real.rpow_nonneg (zero_le_one.trans hN1) _)).trans hcalc⟩
  exact hall t G hr hc hbudget S hS

end DirectedCycles
