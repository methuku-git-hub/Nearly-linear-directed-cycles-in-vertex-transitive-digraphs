module

public import DirectedCycles.PrimeQuotientStep

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Prime character rank extended by zero to nonprimes. -/
noncomputable def primeRank (G : Type*) [Group G] (p : ℕ) : ℕ :=
  if hp : p.Prime then @primeCharacterDimension G _ p ⟨hp⟩ else 0

theorem primeRank_of_prime (G : Type*) [Group G] (p : ℕ) [hp : Fact p.Prime] :
    primeRank G p = primeCharacterDimension G p := by
  simp only [primeRank,hp.out,dite_true]

/-- Sum of prime dimensions through a fixed cutoff. A coarse r(P+1) bound
suffices for the uniform constants and avoids any analytic prime-count input. -/
noncomputable def primeBudget (G : Type*) [Group G] (P : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (P+1), primeRank G p

theorem primeRank_le_rank {G : Type*} [Group G] [Finite G] (p : ℕ) :
    primeRank G p ≤ Group.rank G := by
  unfold primeRank
  split_ifs with hp
  · let : Fact p.Prime := ⟨hp⟩
    exact primeCharacterDimension_le_rank p
  · exact Nat.zero_le _

theorem primeBudget_le_rank_bound {G : Type*} [Group G] [Finite G]
    (r P : ℕ) (hr : Group.rank G ≤ r) : primeBudget G P ≤ r*(P+1) := by
  have h := Finset.sum_le_sum (s := Finset.range (P+1))
    (fun p _ => (primeRank_le_rank (G := G) p).trans hr)
  simpa only [primeBudget,Finset.sum_const,Finset.card_range,smul_eq_mul,Nat.mul_comm] using h

theorem primeRank_quotient_le {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (q : G →* H) (hq : Function.Surjective q) (p : ℕ) : primeRank H p ≤ primeRank G p := by
  unfold primeRank
  split_ifs with hp
  · let : Fact p.Prime := ⟨hp⟩
    exact primeCharacterDimension_quotient_le p q hq
  · exact le_rfl

theorem primeBudget_quotient_le {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (q : G →* H) (hq : Function.Surjective q) (P : ℕ) : primeBudget H P ≤ primeBudget G P :=
  Finset.sum_le_sum (fun p _ => primeRank_quotient_le q hq p)

/-- A chosen prime at most P consumes one unit of the cutoff budget. -/
theorem primeBudget_drop {G : Type*} [Group G] [Finite G]
    (p P : ℕ) [Fact p.Prime] (hpP : p ≤ P) (a : G)
    (hdrop : primeCharacterDimension (G ⧸ elementClosure a) p + 1 = primeCharacterDimension G p) :
    primeBudget (G ⧸ elementClosure a) P + 1 ≤ primeBudget G P := by
  have hstrict : primeBudget (G ⧸ elementClosure a) P < primeBudget G P := by
    apply Finset.sum_lt_sum
    · intro q _
      exact primeRank_quotient_le (QuotientGroup.mk' (elementClosure a))
        (QuotientGroup.mk'_surjective (elementClosure a)) q
    · refine ⟨p,Finset.mem_range.mpr (by omega),?_⟩
      rw [primeRank_of_prime,primeRank_of_prime]
      omega
  omega

/-- Zero budget excludes every prime divisor at or below the cutoff. -/
theorem no_small_primes_of_zero_budget {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (P : ℕ) (hz : primeBudget G P = 0) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card G → P < p := by
  intro p hp hdvd
  let : Fact p.Prime := ⟨hp⟩
  by_contra he
  have hpP : p ≤ P := by omega
  obtain ⟨a,_,_,hdrop,_,_⟩ := nilpotent_prime_quotient_step (Set.univ : Set G)
    (by simp) p hdvd
  have h := primeBudget_drop p P hpP a hdrop
  rw [hz] at h
  omega

end DirectedCycles
