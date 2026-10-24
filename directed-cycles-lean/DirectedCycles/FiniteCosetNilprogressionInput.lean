import DirectedCycles.CosetNilprogression
import DirectedCycles.FiniteNilpotentLargeModel

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- The finite global qualitative BGT coset-nilprogression theorem in
actual signed-word coordinates. Its proof is finite_coset_nilprogression_theorem
in FiniteCosetNilprogressionTheorem. -/
def FiniteCosetNilprogressionTheorem : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ r c M : ℕ, 1 ≤ M ∧
    ∀ (G : Type) [Group G] [Finite G] (A : Set G),
      IsApproximateSubgroup K A →
      ∃ r' c' : ℕ, ∃ P : CosetNilprogression G r' c',
        r' ≤ r ∧ c' ≤ c ∧ P.carrier ⊆ A^4 ∧ Nat.card A ≤ M*Nat.card P.carrier

/-- All finite model properties are derived from an actual contained
coset nilprogression, including quotient nilpotence from generator laws
and rank from an explicitly bounded generating tuple. -/
theorem finite_large_model_of_coset_nilprogression (hBGT : FiniteCosetNilprogressionTheorem) :
    FiniteNilpotentLargeModel := by
  intro K hK
  obtain ⟨r,c,M,hM,hbgt⟩ := hBGT K hK
  refine ⟨r,c,M,hM,?_⟩
  intro G _ _ A hA
  obtain ⟨r',c',P,hr,hc,hPA,hdensity⟩ := hbgt G A hA
  obtain ⟨hNil,hclass⟩ := P.quotient_nilpotent
  refine ⟨P.U,P.H,P.hHU,P.normal,hNil,P.generatorSet,P.carrier,
    P.subgroup_subset_carrier.trans hPA,P.generatorSet_subset_carrier.trans hPA,
    P.generatorSet_card_le.trans hr,hPA,P.carrier_subset_U,P.carrier_subset_generated,
    hdensity,P.quotient_rank_le.trans hr,hclass.trans hc⟩

end DirectedCycles
