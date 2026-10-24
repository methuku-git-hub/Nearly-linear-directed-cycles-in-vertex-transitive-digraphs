import DirectedCycles.CosetProgressionQuotientLift

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Kernel restoration allows different sets for the density comparison
and the containment window. Both refer to the actual quotient map. -/
theorem quotient_coset_progression_lift_density {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (A B T : Set G) (hKT : (K : Set G)*B ⊆ T)
    {r c : ℕ} (Q : CosetNilprogression (G ⧸ K) r c)
    (hQ : Q.carrier ⊆ (QuotientGroup.mk' K) '' B) (J : ℕ)
    (hcard : Nat.card ((QuotientGroup.mk' K) '' A) ≤ J*Nat.card Q.carrier) :
    ∃ P : CosetNilprogression G r c, P.carrier ⊆ T ∧ Nat.card A ≤ J*Nat.card P.carrier := by
  let q := QuotientGroup.mk' K
  let P := preimageCosetNilprogression q (QuotientGroup.mk'_surjective K) Q
  have hpre : P.carrier = q ⁻¹' Q.carrier := preimageCosetNilprogression_carrier q _ Q
  have hsub : P.carrier ⊆ T := by
    rw [hpre]
    apply Set.Subset.trans (Set.preimage_mono hQ)
    rw [quotient_preimage_image_eq_mul]
    exact hKT
  have hA : A ⊆ q ⁻¹' (q '' A) := fun a ha => ⟨a,ha,rfl⟩
  have hacard : Nat.card A ≤ Nat.card K * Nat.card (q '' A) := by
    have hh := Nat.card_le_card_of_injective (Set.inclusion hA) (Set.inclusion_injective hA)
    exact hh.trans_eq (QuotientGroup.card_preimage_mk K (q '' A))
  have hpCard : Nat.card P.carrier = Nat.card K*Nat.card Q.carrier := quotient_preimage_progression_card K Q
  refine ⟨P,hsub,?_⟩
  calc
    Nat.card A ≤ Nat.card K * Nat.card (q '' A) := hacard
    _ ≤ Nat.card K * (J*Nat.card Q.carrier) := Nat.mul_le_mul_left _ hcard
    _ = J*Nat.card P.carrier := by rw [hpCard]; ring
end DirectedCycles
