import DirectedCycles.AbelianLargeModelReduction
import DirectedCycles.FiniteBGTCorollary

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- A single finite qualitative consequence of a large contained coset
nilprogression. Its proof is finite_nilpotent_large_model in
FiniteStructuralTheorems; all constants precede G and A. -/
def FiniteNilpotentLargeModel : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ r c M : ℕ, 1 ≤ M ∧
    ∀ (G : Type) [Group G] [Finite G] (A : Set G),
      IsApproximateSubgroup K A →
      ∃ (U H : Subgroup G) (_hHU : H ≤ U)
        (_hH : (H.subgroupOf U).Normal)
        (_hNil : Group.IsNilpotent (U ⧸ H.subgroupOf U))
        (F : Finset G) (B : Set G),
        (H : Set G) ⊆ A^4 ∧ (F : Set G) ⊆ A^4 ∧ F.card ≤ r ∧
        B ⊆ A^4 ∧ B ⊆ U ∧ B ⊆ Subgroup.closure ((H : Set G) ∪ (F : Set G)) ∧
        Nat.card A ≤ M*Nat.card B ∧
        Group.rank (U ⧸ H.subgroupOf U) ≤ r ∧
        Group.nilpotencyClass (U ⧸ H.subgroupOf U) ≤ c

/-- Ruzsa covering bounds the number of cosets of a subgroup containing
a dense short set. No assumption that the subgroup is normal is made. -/
theorem dense_short_set_coset_bound {G : Type*} [Group G] [Finite G]
    (A B : Set G) (K : ℝ) (M : ℕ) (hA : IsApproximateSubgroup K A)
    (hBA : B ⊆ A^4) (hdensity : Nat.card A ≤ M*Nat.card B)
    (U : Subgroup G) (hBU : B ⊆ U) :
    Nat.card ↥((Quotient.mk'' : G → G ⧸ U) '' A) ≤ ⌈K^4*(M : ℝ)⌉₊ := by
  obtain ⟨X,_hXA,hX,hcover⟩ := dense_short_set_cover A B K M hA hBA hdensity
  have hsub : (Quotient.mk'' : G → G ⧸ U) '' A ⊆ Quotient.mk'' '' X := by
    rintro z ⟨a,ha,rfl⟩
    obtain ⟨x,hx,b,hb,rfl⟩ := hcover ha
    obtain ⟨b,hb,c,hc,rfl⟩ := hb
    exact ⟨x,hx,(QuotientGroup.mk_mul_of_mem x (U.div_mem (hBU hb) (hBU hc))).symm⟩
  have hcard : Nat.card ↥((Quotient.mk'' : G → G ⧸ U) '' A) ≤ Nat.card X := by
    exact (Set.ncard_le_ncard hsub).trans (Set.ncard_image_le X.toFinite)
  have hcardreal : (Nat.card ↥((Quotient.mk'' : G → G ⧸ U) '' A) : ℝ) ≤ Nat.card X := by
    exact_mod_cast hcard
  have hreal := hcardreal.trans hX
  exact_mod_cast hreal.trans (Nat.le_ceil _)

/-- The ordinary finite classification input follows from the common
large-model statement. -/
theorem finite_classification_of_large_model (hModel : FiniteNilpotentLargeModel) :
    FiniteApproximateClassification := by
  intro K hK
  obtain ⟨r,c,M,_hM,hmodel⟩ := hModel K hK
  refine ⟨⌈K^4*(M : ℝ)⌉₊+1,r,c,by omega,?_⟩
  intro G _ _ A hA
  obtain ⟨U,H,hHU,hHn,hNil,_F,B,hH,_hF,_hc,hBA,hBU,_hBgen,hdensity,hr,hclass⟩ := hmodel G A hA
  refine ⟨U,H,hHU,hHn,hNil,hH,?_,hr,hclass⟩
  exact (dense_short_set_coset_bound A B K M hA hBA hdensity U hBU).trans (by omega)

/-- The abelian structural input is a specialization of the same common
large model. It need not be introduced as an independent theorem. -/
theorem finite_abelian_large_model_of_nilpotent (hModel : FiniteNilpotentLargeModel) :
    FiniteAbelianLargeModel := by
  intro K hK
  obtain ⟨r,_c,M,hM,hmodel⟩ := hModel K hK
  refine ⟨r,M,hM,?_⟩
  intro G _ _ A hA
  obtain ⟨_U,H,_hHU,_hHn,_hNil,F,B,hH,hF,hcard,hBA,_hBU,hBgen,hdensity,_hr,_hc⟩ := hmodel G A hA
  exact ⟨H,F,B,hH,hF,hcard,hBA,hBgen,hdensity⟩

end DirectedCycles
