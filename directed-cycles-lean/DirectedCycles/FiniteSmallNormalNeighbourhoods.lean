import DirectedCycles.FiniteSmallNeighbourhoods
import DirectedCycles.UniformNormalCoreDensity

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace FiniteAlmostPeriods

/-- The finite global small normal-neighbourhood theorem. All constants
are chosen before the group and sets. Both conjugation and coset orders
are explicit in the underlying finite normal-core argument. -/
theorem finite_small_normal_neighbourhoods (K K' δ : ℝ) (m : ℕ)
    (hK : 1 ≤ K) (hK' : 1 ≤ K') (hδ : 0 < δ) :
    ∃ L ρ : ℝ, 1 ≤ L ∧ 0 < ρ ∧
      ∀ (G : Type*) [Group G] [DecidableEq G] (A R : Finset G),
      IsApproximateSubgroup K (A : Set G) → IsApproximateSubgroup K' (R : Set G) →
      R ⊆ A^4 → δ*A.card ≤ R.card →
      ∃ T : Finset G, IsApproximateSubgroup L (T : Set G) ∧
        ρ*A.card ≤ T.card ∧
        ∀ x ∈ (A : Set G)^4, ∀ g ∈ (T : Set G)^m, x⁻¹*g*x ∈ (R : Set G)^4 := by
  classical
  obtain ⟨L₀,δ₀,hL₀,hδ₀,hsmall⟩ := finite_small_neighbourhoods K' hK' (4*m+8)
  let τ := δ₀*δ
  have hτ : 0 < τ := mul_pos hδ₀ hδ
  let N := ⌈K^19/τ⌉₊+1
  obtain ⟨ρ,hρ,hcore⟩ := uniform_normalCore_density K τ hK hτ N
  let L := max 1 ((K^15/ρ)^3)
  refine ⟨L,ρ,le_max_left _ _,hρ,?_⟩
  intro G _ _ A R hA hR hRA hRcard
  have hK0 : 0 < K := by linarith
  obtain ⟨S,hS,hScard,hSpow⟩ := hsmall G R hR
  have hSi : S⁻¹ = S := by
    apply Finset.coe_injective
    simpa only [Finset.coe_inv] using hS.inv_eq_self
  have hR4 : (R : Set G)^4 ⊆ (A : Set G)^16 := by
    calc
      (R : Set G)^4 ⊆ ((A : Set G)^4)^4 := Set.pow_subset_pow_left (by exact_mod_cast hRA)
      _ = (A : Set G)^16 := by rw [← pow_mul]
  have hSshort : (S : Set G) ⊆ (R : Set G)^4 :=
    (Set.subset_pow hS.one_mem (by omega : 4*m+8 ≠ 0)).trans hSpow
  have hSA : S ⊆ A^16 := by exact_mod_cast hSshort.trans hR4
  have hSd : τ*A.card ≤ (S.card : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hRcard hδ₀.le
    dsimp [τ]
    nlinarith
  obtain ⟨X,hX1,hXA,hXN,hcover⟩ := approximate_power_left_cover A S K τ hA hτ hSA hSd hSi
  let T := normalCoreSet S X
  have hT1 : 1 ∈ T := normalCoreSet_one S X hS.one_mem
  have hTi : T⁻¹ = T := normalCoreSet_symm S X hSi
  have hTcard : ρ*A.card ≤ (T.card : ℝ) := hcore G A S X hA hSA hSd hSi hX1 hXA hXN
  have hT3 : (T : Set G)^3 ⊆ (A : Set G)^16 := by
    calc
      (T : Set G)^3 ⊆ ((S : Set G)^2)^3 :=
        Set.pow_subset_pow_left (by exact_mod_cast normalCoreSet_subset S X)
      _ = (S : Set G)^6 := by rw [← pow_mul]
      _ ⊆ (S : Set G)^(4*m+8) := Set.pow_subset_pow_right hS.one_mem (by omega)
      _ ⊆ (R : Set G)^4 := hSpow
      _ ⊆ (A : Set G)^16 := hR4
  have htrip : ((T^3).card : ℝ) ≤ (K^15/ρ)*T.card := by
    have hsub : T^3 ⊆ A^16 := by exact_mod_cast hT3
    have hc : ((T^3).card : ℝ) ≤ (A^16).card := by exact_mod_cast Finset.card_le_card hsub
    have hp : ((A^16).card : ℝ) ≤ K^15*A.card := by simpa using hA.card_pow_le (n := 16)
    have hdiv : (A.card : ℝ) ≤ T.card/ρ := (le_div_iff₀ hρ).mpr (by nlinarith [hTcard])
    calc
      ((T^3).card : ℝ) ≤ K^15*A.card := hc.trans hp
      _ ≤ K^15*(T.card/ρ) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = (K^15/ρ)*T.card := by ring
  refine ⟨T^2,?_,?_,?_⟩
  · have hh := IsApproximateSubgroup.of_small_tripling hT1 hTi htrip
    simpa only [Finset.coe_pow] using hh.mono (le_max_right 1 ((K^15/ρ)^3))
  · have hh : T.card ≤ (T^2).card := by
      simpa only [pow_two] using (Finset.card_le_card_mul_right ⟨1,hT1⟩ : T.card ≤ (T*T).card)
    exact hTcard.trans (by exact_mod_cast hh)
  · intro x hx g hg
    have hgp : g ∈ (T : Set G)^(2*m) := by simpa only [Finset.coe_pow,← pow_mul] using hg
    have hh := normalCoreSet_conjugate_power S X ((A : Set G)^4) hSi hcover (2*m) x hx g hgp
    have hp : (S : Set G)^(2*(2*m)+4) ⊆ (S : Set G)^(4*m+8) :=
      Set.pow_subset_pow_right hS.one_mem (by omega)
    exact hSpow (hp hh)

end FiniteAlmostPeriods
end DirectedCycles
