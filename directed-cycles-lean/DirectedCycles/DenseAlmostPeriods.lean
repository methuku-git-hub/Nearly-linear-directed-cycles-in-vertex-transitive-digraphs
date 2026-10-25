module

public import DirectedCycles.TranslateEnergy

@[expose] public section

set_option autoImplicit false
open scoped Pointwise BigOperators
namespace DirectedCycles
namespace FiniteAlmostPeriods
variable {G : Type*} [Group G] [DecidableEq G]

theorem mul_inter_translate_subset (A B : Finset G) (g : G) :
    A*(B ∩ rightTranslate B g) ⊆ (A*B) ∩ rightTranslate (A*B) g := by
  intro x hx
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp hx
  obtain ⟨hbB,hbg⟩ := Finset.mem_inter.mp hb
  apply Finset.mem_inter.mpr
  constructor
  · exact Finset.mul_mem_mul ha hbB
  · obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hbg
    exact Finset.mem_image.mpr ⟨a*c,Finset.mul_mem_mul ha hc,mul_assoc _ _ _⟩

/-- The right-translate convention forces the period to be a*a0^{-1}.
This identity keeps the multiplication order explicit. -/
theorem overlap_right_period (B : Finset G) (a a₀ : G) :
    (rightTranslate B a₀ ∩ rightTranslate B a).card =
      (B ∩ rightTranslate B (a*a₀⁻¹)).card := by
  rw [← card_rightTranslate (rightTranslate B a₀ ∩ rightTranslate B a) a₀⁻¹,
    rightTranslate_inter,← rightTranslate_mul,← rightTranslate_mul]
  simp only [mul_inv_cancel,rightTranslate_one]

theorem dense_almost_periods (A B : Finset G) (K ε t δ : ℝ)
    (hA : IsApproximateSubgroup K (A : Set G)) (hε : 0 ≤ ε)
    (ht : 0 ≤ t) (hδ : 0 ≤ δ) (hBA : B ⊆ A) (hB : t*A.card ≤ B.card)
    (hscale : 2*δ*K ≤ t^2)
    (hmin : ∀ C : Finset G, C ⊆ A → δ*A.card ≤ C.card →
      (1-ε)*(A*B).card ≤ (A*C).card) :
    ∃ S : Finset G, 1 ∈ S ∧ S⁻¹ = S ∧ S ⊆ A^2 ∧ δ*A.card ≤ S.card ∧
      ∀ g ∈ S, (defect (A*B) g : ℝ) ≤ ε*(A*B).card := by
  classical
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hA.one_le
  have hprod : ((B*A).card : ℝ) ≤ K*A.card := by
    have hc : (B*A).card ≤ (A*A).card :=
      Finset.card_le_card (Finset.mul_subset_mul hBA (Finset.Subset.refl _))
    exact (show ((B*A).card : ℝ) ≤ (A*A).card from by exact_mod_cast hc).trans hA.card_mul_self_le
  obtain ⟨a₀,ha₀,hCcard⟩ := many_overlapping_translates A B K t δ
    ⟨1,hA.one_mem⟩ hBA hK ht hδ hB hprod hscale
  let C := {a ∈ A | δ*A.card ≤ ((rightTranslate B a₀ ∩ rightTranslate B a).card : ℝ)}
  let S := {g ∈ A^2 | (defect (A*B) g : ℝ) ≤ ε*(A*B).card}
  have hAsymm : A⁻¹ = A := by
    apply Finset.coe_injective
    simpa only [Finset.coe_inv] using hA.inv_eq_self
  have hA2symm : (A^2)⁻¹ = A^2 := by rw [← inv_pow,hAsymm]
  have hCS : C.image (fun a => a*a₀⁻¹) ⊆ S := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨haA,haC⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    constructor
    · rw [pow_two]
      exact Finset.mul_mem_mul haA (by
        have : a₀⁻¹ ∈ A⁻¹ := by simpa using ha₀
        simpa only [hAsymm] using this)
    · let D := B ∩ rightTranslate B (a*a₀⁻¹)
      have hDA : D ⊆ A := Finset.inter_subset_left.trans hBA
      have hDcard : δ*A.card ≤ (D.card : ℝ) := by
        simpa only [D,overlap_right_period B a a₀] using haC
      have hl := hmin D hDA hDcard
      have hu : ((A*D).card : ℝ) ≤ ((A*B) ∩ rightTranslate (A*B) (a*a₀⁻¹)).card := by
        exact_mod_cast Finset.card_le_card (mul_inter_translate_subset A B (a*a₀⁻¹))
      have he : (defect (A*B) (a*a₀⁻¹) : ℝ) +
          ((A*B) ∩ rightTranslate (A*B) (a*a₀⁻¹)).card = (A*B).card := by
        exact_mod_cast defect_add_overlap (A*B) (a*a₀⁻¹)
      nlinarith
  refine ⟨S,?_,?_,?_,?_,?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨by simpa using Finset.one_mem_pow hA.one_mem,by simpa only [defect_one,Nat.cast_zero] using mul_nonneg hε (Nat.cast_nonneg (A*B).card)⟩
  · ext g
    have he : g⁻¹ ∈ A^2 ↔ g ∈ A^2 := by rw [← Finset.mem_inv',hA2symm]
    simp only [Finset.mem_inv',S,Finset.mem_filter,he,defect_inv]
  · exact Finset.filter_subset _ _
  · have hh : C.card ≤ S.card := by
      rw [← Finset.card_image_of_injective C (mul_left_injective a₀⁻¹)]
      exact Finset.card_le_card hCS
    exact hCcard.trans (by exact_mod_cast hh)
  · intro g hg
    exact (Finset.mem_filter.mp hg).2

end FiniteAlmostPeriods
end DirectedCycles
