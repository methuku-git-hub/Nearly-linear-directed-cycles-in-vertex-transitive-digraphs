module

public import DirectedCycles.DenseAlmostPeriods
public import DirectedCycles.ExpansionMinimizers

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace FiniteAlmostPeriods

/-- The finite global small-neighbourhood theorem, with uniform constants.
The proof uses corrected right translates, Cauchy--Schwarz, scale selection,
and the library's proved Ruzsa small-tripling theorem. -/
theorem finite_small_neighbourhoods (K : ℝ) (hK : 1 ≤ K) (m : ℕ) :
    ∃ L δ : ℝ, 1 ≤ L ∧ 0 < δ ∧
      ∀ (G : Type*) [Group G] [DecidableEq G] (A : Finset G),
      IsApproximateSubgroup K (A : Set G) →
      ∃ S : Finset G, IsApproximateSubgroup L (S : Set G) ∧
        δ*A.card ≤ S.card ∧ (S : Set G)^m ⊆ (A : Set G)^4 := by
  classical
  let ε : ℝ := 1/(10*(m : ℝ)+10)
  have hden : (0 : ℝ) < 10*(m : ℝ)+10 := by positivity
  have hε : 0 < ε := one_div_pos.mpr hden
  obtain ⟨δ,hδ,hscale⟩ := uniform_expansion_scale K ε hK hε
  let L := max 1 ((K^3/δ)^3)
  refine ⟨L,δ,le_max_left _ _,hδ,?_⟩
  intro G _ _ A hA
  obtain ⟨t,d,B,ht,ht1,hd,hδd,hBA,hB,hmin⟩ := hscale G A hA
  have hd0 : 0 < d := by rw [hd]; exact div_pos (sq_pos_of_pos ht) (by linarith)
  have hds : 2*d*K ≤ t^2 := by
    rw [hd]
    have hK0 : K ≠ 0 := by linarith
    field_simp
    norm_num
  obtain ⟨S,hS1,hSinv,hSA,hSd,hperiod⟩ :=
    dense_almost_periods A B K ε t d hA hε.le ht.le hd0.le hBA hB hds hmin
  have hScard : δ*A.card ≤ (S.card : ℝ) :=
    (mul_le_mul_of_nonneg_right hδd (Nat.cast_nonneg A.card)).trans hSd
  have hAcard : (0 : ℝ) < A.card := by
    exact_mod_cast (show A.Nonempty from ⟨1,hA.one_mem⟩).card_pos
  have hBnon : B.Nonempty := Finset.card_pos.mp (by
    have : (0 : ℝ) < B.card := (mul_pos ht hAcard).trans_le hB
    exact_mod_cast this)
  have hABcard : (0 : ℝ) < (A*B).card := by
    exact_mod_cast (show (A*B).Nonempty from Finset.mul_nonempty.mpr ⟨⟨1,hA.one_mem⟩,hBnon⟩).card_pos
  have hAB : ((A*B : Finset G) : Set G) ⊆ (A : Set G)^2 := by
    rw [Finset.coe_mul,pow_two]
    exact Set.mul_subset_mul_left hBA
  have hdiff : ((A*B : Finset G) : Set G)⁻¹ * ((A*B : Finset G) : Set G) ⊆
      (A : Set G)^4 := by
    calc
      _ ⊆ ((A : Set G)^2)⁻¹ * (A : Set G)^2 :=
        Set.mul_subset_mul (Set.inv_subset_inv.mpr hAB) hAB
      _ = (A : Set G)^4 := by rw [← inv_pow,hA.inv_eq_self,← pow_add]
  have hpowers : ∀ n : ℕ, n ≤ 2*m+3 → (S : Set G)^n ⊆ (A : Set G)^4 := by
    intro n hn
    apply (pow_subset_difference (A*B) (S : Set G) (ε*(A*B).card) n hperiod ?_).trans hdiff
    have hnr : (n : ℝ) ≤ 2*m+3 := by exact_mod_cast hn
    have hne : (n : ℝ)*ε < 1 := by
      dsimp [ε]
      rw [mul_one_div]
      apply (div_lt_one hden).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    nlinarith
  have htrip : ((S^3).card : ℝ) ≤ (K^3/δ)*S.card := by
    have hsub : S^3 ⊆ A^4 := by
      exact_mod_cast hpowers 3 (by omega)
    have hc : ((S^3).card : ℝ) ≤ (A^4).card := by exact_mod_cast Finset.card_le_card hsub
    have hpow : ((A^4).card : ℝ) ≤ K^3*A.card := by simpa using hA.card_pow_le (n := 4)
    have hdiv : (A.card : ℝ) ≤ S.card/δ := (le_div_iff₀ hδ).mpr (by nlinarith [hScard])
    calc
      ((S^3).card : ℝ) ≤ K^3*A.card := hc.trans hpow
      _ ≤ K^3*(S.card/δ) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = (K^3/δ)*S.card := by ring
  have happrox := IsApproximateSubgroup.of_small_tripling hS1 hSinv htrip
  refine ⟨S^2,?_,?_,?_⟩
  · simpa only [Finset.coe_pow] using happrox.mono (le_max_right 1 ((K^3/δ)^3))
  · have hh : S.card ≤ (S^2).card := by
      simpa only [pow_two] using (Finset.card_le_card_mul_right ⟨1,hS1⟩ : S.card ≤ (S*S).card)
    exact hScard.trans (by exact_mod_cast hh)
  · simpa only [Finset.coe_pow,← pow_mul] using hpowers (2*m) (by omega)

end FiniteAlmostPeriods
end DirectedCycles
