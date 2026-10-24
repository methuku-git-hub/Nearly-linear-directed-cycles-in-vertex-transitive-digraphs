import DirectedCycles.PrimeCharacterQuotients

set_option autoImplicit false
namespace DirectedCycles

/-- A nonzero value in the prime-field character forces the selected prime
to divide the order of the normal closure of that label. -/
theorem prime_dvd_normalClosure_of_character {G : Type*} [Group G] [Finite G]
    (p : ℕ) [hp : Fact p.Prime] (a : G) (f : PrimeCharacters G p)
    (hf : f (Additive.ofMul a) ≠ 0) : p ∣ Nat.card (elementClosure a) := by
  let fm := f.toMultiplicativeRight
  have hfa : fm a ≠ 1 := by
    intro he
    apply hf
    exact congrArg Multiplicative.toAdd he
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
  have horder : orderOf (fm a) = p :=
    (orderOf_eq_card_of_zpowers_eq_top (zpowers_eq_top_of_prime_card hcard hfa)).trans hcard
  have hdvd : p ∣ orderOf a := by rw [← horder]; exact orderOf_map_dvd fm a
  exact hdvd.trans ((elementClosure a).orderOf_dvd_natCard (mem_elementClosure a))

/-- The quotient-chain step, proved through prime characters. It decreases
the selected dimension exactly once and strictly decreases the group order. -/
theorem nilpotent_prime_quotient_step {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (S : Set G) (hS : Subgroup.closure S = ⊤) (p : ℕ) [hp : Fact p.Prime]
    (hdvd : p ∣ Nat.card G) :
    ∃ a ∈ S, p ∣ Nat.card (elementClosure a) ∧
      primeCharacterDimension (G ⧸ elementClosure a) p + 1 = primeCharacterDimension G p ∧
      Nat.card (G ⧸ elementClosure a) < Nat.card G ∧
      (elementClosure a = ⊤ → Subgroup.zpowers a = ⊤) := by
  obtain ⟨f,hf⟩ := nilpotent_prime_character p hdvd
  obtain ⟨a,ha,hfa⟩ := nonzero_primeCharacter_on_generator S hS f hf
  have hpK := prime_dvd_normalClosure_of_character p a f hfa
  refine ⟨a,ha,hpK,primeCharacterDimension_normalClosure_drop p a f hfa,?_,
    elementClosure_eq_top_implies_cyclic a⟩
  have hple : p ≤ Nat.card (elementClosure a) := Nat.le_of_dvd Nat.card_pos hpK
  rw [(elementClosure a).card_eq_card_quotient_mul_card_subgroup]
  exact lt_mul_of_one_lt_right Nat.card_pos (hp.out.one_lt.trans_le hple)

end DirectedCycles
