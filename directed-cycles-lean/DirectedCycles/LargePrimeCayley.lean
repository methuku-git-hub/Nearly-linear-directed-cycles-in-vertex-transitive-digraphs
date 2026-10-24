import DirectedCycles.PrimeBudget
import DirectedCycles.SpanningCycleLift
import DirectedCycles.CyclicGeneratorCycle
import DirectedCycles.PrimeCutoffFactors
import DirectedCycles.PrimeLossArithmetic
import DirectedCycles.NilpotentRanks

set_option autoImplicit false
universe u
namespace DirectedCycles

/-- Strong induction on the actual group order replaces the written quotient
chain. Every selected quotient is strict, and prime-character budgets account
for all constant losses while the spanning invariant is preserved. -/
theorem large_prime_cayley_budget (r c n : ℕ) (hcn : c ≤ n)
    (alpha eta : ℝ) (ha : 0 < alpha) (ha1 : alpha ≤ 1) (he : 0 ≤ eta)
    (P : ℕ) (hcut : ∀ K : ℝ, (P : ℝ) < K → K^(-eta) ≤ alpha)
    (hlower : ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H],
      Group.rank H ≤ ∑ i ∈ Finset.range c, r^(i+1) →
      Group.nilpotencyClass H ≤ c/2 → LayerSpanningBound H (n+1) (4*alpha) eta)
    (G : Type u) [Group G] [Finite G] [Group.IsNilpotent G] [Nontrivial G]
    (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c)
    (hp : AbovePrimeCutoff G (n+1)) (S : Set G) (hS : Subgroup.closure S = ⊤) :
    ∃ C : Cycle (CayleyDigraph S),
      alpha^(primeBudget G P)*(Nat.card G : ℝ)^(1-2*eta) ≤ C.length ∧
      SpansTruncation (n+1) (Set.range C.vertex) := by
  have hall : ∀ N : ℕ, ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H] [Nontrivial H],
      Nat.card H = N → Group.rank H ≤ r → Group.nilpotencyClass H ≤ c →
      AbovePrimeCutoff H (n+1) → ∀ A : Set H, Subgroup.closure A = ⊤ →
      ∃ C : Cycle (CayleyDigraph A),
        alpha^(primeBudget H P)*(Nat.card H : ℝ)^(1-2*eta) ≤ C.length ∧
        SpansTruncation (n+1) (Set.range C.vertex) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro H instH instF instNil instNT hcard hrH hcH hpH A hA
      have hgt : 1 < Nat.card H := by
        let : Fintype H := Fintype.ofFinite H
        simpa only [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := H)
      let p := (Nat.card H).minFac
      have hprime : p.Prime := Nat.minFac_prime (by omega)
      let : Fact p.Prime := ⟨hprime⟩
      obtain ⟨a,haA,hpK,hdrop,hlt,hcyclic⟩ :=
        nilpotent_prime_quotient_step A hA p (Nat.minFac_dvd _)
      by_cases htop : elementClosure a = ⊤
      · obtain ⟨C,hC,hspan⟩ := cyclic_generator_cycle A a haA (hcyclic htop)
        refine ⟨C,?_,hspan (n+1)⟩
        rw [hC]
        have hb : alpha^(primeBudget H P) ≤ 1 := pow_le_one₀ ha.le ha1
        exact (mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) hb).trans
          (cardinal_rpow_le_card (2*eta) (by positivity))
      · let K := elementClosure a
        let B := elementCommutators a
        let q := QuotientGroup.mk' K
        let : Nontrivial (H ⧸ K) := QuotientGroup.nontrivial_iff.mpr htop
        have hrQ : Group.rank (H ⧸ K) ≤ r :=
          (Group.rank_le_of_surjective q (QuotientGroup.mk'_surjective K)).trans hrH
        have hcQ : Group.nilpotencyClass (H ⧸ K) ≤ c :=
          (Group.nilpotencyClass_quotient_le K).trans hcH
        have hpQ : AbovePrimeCutoff (H ⧸ K) (n+1) := hpH.of_card_dvd K.card_quotient_dvd_card
        have hqA : Subgroup.closure (q '' A) = ⊤ := by
          rw [← MonoidHom.map_closure,hA,Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
        obtain ⟨Q,hQ,hQspan⟩ := ih (Nat.card (H ⧸ K)) (by simpa only [← hcard] using hlt)
          (H ⧸ K) rfl hrQ hcQ hpQ (q '' A) hqA
        have hnonid : a ≠ 1 := nonidentity_of_prime_dvd_elementClosure a p hprime hpK
        have hh := hpH.elementClosure_factor_large a hnonid
        have hrB : Group.rank B ≤ ∑ i ∈ Finset.range c, r^(i+1) :=
          nilpotent_subgroup_rank_bound r c hrH hcH B
        have hcB : Group.nilpotencyClass B ≤ c/2 :=
          commutator_subgroup_class_le_half B (elementCommutators_le_derived a) c hcH
        obtain ⟨C,hC,_,hCspan⟩ := spanning_cycle_lift a A haA n (hcH.trans hcn) hh Q hQspan
          (4*alpha) eta (by positivity) (hlower B hrB hcB) hpH
        refine ⟨C,?_,C.spans_of_generatorTails a (n+1) hCspan⟩
        have hquotbudget : primeBudget (H ⧸ K) P ≤ primeBudget H P :=
          primeBudget_quotient_le q (QuotientGroup.mk'_surjective K) P
        have hcharge : primeBudget (H ⧸ K) P+1 ≤ primeBudget H P ∨
            (Nat.card K : ℝ)^(-eta) ≤ alpha := by
          by_cases hsmall : p ≤ P
          · exact Or.inl (primeBudget_drop p P hsmall a hdrop)
          · apply Or.inr
            apply hcut
            have hple : p ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos hpK
            exact_mod_cast (show P < Nat.card K by omega)
        have hBK : (Nat.card B : ℝ) ≤ Nat.card K := by
          exact_mod_cast (Nat.le_of_dvd (Nat.card_pos (α := K))
            (Subgroup.card_dvd_of_le (show B ≤ K from le_sup_right)))
        have hK1 : (1 : ℝ) ≤ Nat.card K := by exact_mod_cast (Nat.card_pos (α := K))
        have hqpos : (0 : ℝ) < Nat.card (H ⧸ K) := by exact_mod_cast (Nat.card_pos (α := H ⧸ K))
        have hBpos : (0 : ℝ) < Nat.card B := by exact_mod_cast (Nat.card_pos (α := B))
        have hL : alpha*(Q.length : ℝ)*Nat.card K*(Nat.card B : ℝ)^(-eta) ≤ C.length := by
          simpa only [mul_div_cancel_left₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using hC
        have hcalc := prime_loss_recurrence alpha eta (Nat.card (H ⧸ K)) (Nat.card K)
          (Nat.card B) Q.length C.length (primeBudget H P) (primeBudget (H ⧸ K) P)
          ha ha1 he hqpos hK1 hBpos hBK hquotbudget hcharge hQ hL
        have hid : (Nat.card H : ℝ) = (Nat.card (H ⧸ K) : ℝ)*Nat.card K := by
          exact_mod_cast K.card_eq_card_quotient_mul_card_subgroup
        rwa [← hid] at hcalc
  exact hall (Nat.card G) G rfl hr hc hp S hS

/-- The prime budget is bounded uniformly by the generator rank and cutoff. -/
theorem large_prime_cayley_uniform (r c n : ℕ) (hcn : c ≤ n)
    (alpha eta : ℝ) (ha : 0 < alpha) (ha1 : alpha ≤ 1) (he : 0 ≤ eta)
    (P : ℕ) (hcut : ∀ K : ℝ, (P : ℝ) < K → K^(-eta) ≤ alpha)
    (hlower : ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H],
      Group.rank H ≤ ∑ i ∈ Finset.range c, r^(i+1) →
      Group.nilpotencyClass H ≤ c/2 → LayerSpanningBound H (n+1) (4*alpha) eta)
    (G : Type u) [Group G] [Finite G] [Group.IsNilpotent G] [Nontrivial G]
    (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c)
    (hp : AbovePrimeCutoff G (n+1)) (S : Set G) (hS : Subgroup.closure S = ⊤) :
    ∃ C : Cycle (CayleyDigraph S),
      alpha^(r*(P+1))*(Nat.card G : ℝ)^(1-2*eta) ≤ C.length ∧
      SpansTruncation (n+1) (Set.range C.vertex) := by
  obtain ⟨C,hC,hspan⟩ := large_prime_cayley_budget r c n hcn alpha eta ha ha1 he P hcut hlower G hr hc hp S hS
  refine ⟨C,?_,hspan⟩
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one ha.le ha1 (primeBudget_le_rank_bound r P hr))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans hC

end DirectedCycles
