import DirectedCycles.QuotientPowerTrapping
import DirectedCycles.QuotientProgressionDensityRestoration

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- The finite strong reduction supplies NSS on the quotient fourth power,
and restores every progression there into the original fifth power with
unchanged rank, class and density factor. -/
theorem strong_finite_enlarged_nss_restoration {G : Type*} [Group G] [Fintype G]
    {K : ℕ} {A : Finset G} (hA : IsStrongFiniteApproximateGroup K A) :
    ∃ H : Subgroup (Subgroup.closure (A : Set G)), ∃ hH : H.Normal,
      let := hH
      let U := Subgroup.closure (A : Set G)
      let B := U.subtype ⁻¹' (A : Set G)
      let q := QuotientGroup.mk' H
      IsApproximateSubgroup (K : ℝ) (q '' B) ∧
      (∀ y : U ⧸ H, (∀ n : ℕ, y^n ∈ (q '' B)^4) → y = 1) ∧
      ∀ r c : ℕ, ∀ Q : CosetNilprogression (U ⧸ H) r c,
        Q.carrier ⊆ (q '' B)^4 → ∀ J : ℕ, Nat.card (q '' B) ≤ J*Nat.card Q.carrier →
        ∃ P : CosetNilprogression G r c,
          P.carrier ⊆ (A : Set G)^5 ∧ Nat.card (A : Set G) ≤ J*Nat.card P.carrier := by
  classical
  obtain ⟨H,hH,hHB,hq,hNSS⟩ := strong_finite_nss_quotient_with_kernel hA
  let := hH
  let U := Subgroup.closure (A : Set G)
  let B := U.subtype ⁻¹' (A : Set G)
  let q := QuotientGroup.mk' H
  have hAU : (A : Set G) ⊆ U := Subgroup.subset_closure
  have himage : U.subtype '' B = (A : Set G) := by
    rw [subtype_image_preimage,Set.inter_eq_left.mpr hAU]
  have hB1 : (1 : U) ∈ B := hA.approximate.one_mem
  have hker : (q.ker : Set U) ⊆ B := by
    intro x hx
    exact hHB ((QuotientGroup.eq_one_iff x).1 hx)
  obtain ⟨S,_hSi,_hsmall,hfirst,_hsecond⟩ := hA.trapping
  have htrap : ∀ x : U, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 → x^j ∈ B^100) → x ∈ B := by
    intro x hx
    apply hfirst
    intro j hj hjmax
    have hh : U.subtype (x^j) ∈ U.subtype '' B^100 := ⟨x^j,hx j hj hjmax,rfl⟩
    rw [Set.image_pow,himage] at hh
    exact hh
  have hqtrap := quotient_fourth_power_trapping q (QuotientGroup.mk'_surjective H) B hB1 hker htrap
  refine ⟨H,hH,hq,quotient_fourth_power_cyclic_nss (q '' B) hqtrap hNSS,?_⟩
  intro r c Q hQ J hcard
  have hKT : (H : Set U)*B^4 ⊆ B^5 := by
    calc
      _ ⊆ B*B^4 := Set.mul_subset_mul_right hHB
      _ = B^5 := by rw [← pow_succ']
  have hQ' : Q.carrier ⊆ q '' (B^4) := by simpa only [Set.image_pow] using hQ
  obtain ⟨R,hR,hRcard⟩ := quotient_coset_progression_lift_density H B (B^4) (B^5) hKT Q hQ' J hcard
  obtain ⟨P,hP,hPcard⟩ := coset_progression_image_of_injective U.subtype U.subtype_injective
    R (B^5) hR (Nat.card B) J hRcard
  have hBAcard : Nat.card B = Nat.card (A : Set G) := by
    rw [← Nat.card_image_of_injective U.subtype_injective,himage]
  rw [Set.image_pow,himage] at hP
  rw [hBAcard] at hPcard
  exact ⟨P,hP,hPcard⟩
end DirectedCycles
