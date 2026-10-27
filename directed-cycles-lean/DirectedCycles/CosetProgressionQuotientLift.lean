module

public import DirectedCycles.CosetProgressionPreimage
public import Mathlib.GroupTheory.Sylow

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Full quotient preimages have the exact finite-kernel factor. -/
theorem quotient_preimage_progression_card {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] {r c : ℕ} (Q : CosetNilprogression (G ⧸ K) r c) :
    Nat.card (preimageCosetNilprogression (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) Q).carrier =
      Nat.card K * Nat.card Q.carrier := by
  rw [preimageCosetNilprogression_carrier]
  exact QuotientGroup.card_preimage_mk K Q.carrier

/-- A full quotient preimage consists exactly of kernel translates of the
original set; this supplies its containment before any density conclusion. -/
theorem quotient_preimage_image_eq_mul {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] (A : Set G) :
    (QuotientGroup.mk' K) ⁻¹' ((QuotientGroup.mk' K) '' A) = (K : Set G)*A := by
  let q := QuotientGroup.mk' K
  ext z
  constructor
  · rintro ⟨a,ha,he⟩
    have hz : z*a⁻¹ ∈ K := by
      apply (QuotientGroup.eq_one_iff _).1
      change q (z*a⁻¹) = 1
      rw [map_mul,map_inv,← he,mul_inv_cancel]
    exact ⟨z*a⁻¹,hz,a,ha,inv_mul_cancel_right z a⟩
  · rintro ⟨k,hk,a,ha,rfl⟩
    refine ⟨a,ha,?_⟩
    have hkq : q k = 1 := (QuotientGroup.eq_one_iff k).2 hk
    change q a = q (k*a)
    rw [map_mul,hkq,one_mul]

/-- Reattach the actual finite kernel while preserving the same rank,
step and density factor. The target containment is proved from the full
kernel translate set. -/
theorem quotient_coset_progression_lift {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (A T : Set G) (hKT : (K : Set G)*A ⊆ T)
    {r c : ℕ} (Q : CosetNilprogression (G ⧸ K) r c)
    (hQ : Q.carrier ⊆ (QuotientGroup.mk' K) '' A) (J : ℕ)
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
