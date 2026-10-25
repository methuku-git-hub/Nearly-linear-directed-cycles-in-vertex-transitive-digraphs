module

public import DirectedCycles.LowerPowerCoverage
public import DirectedCycles.SubgroupSeries

@[expose] public section

set_option autoImplicit false
open scoped BigOperators IsMulCommutative
namespace DirectedCycles

/-- Power coverage in a lower central factor lands in the image of the
factor of the intersected C-series. -/
theorem lowerFactor_power_in_intersected_range {G : Type*} [Group G]
    (C : Subgroup G) (m : ℕ) (hbase : ∀ x : G, x^m ∈ C ⊔ commutator G) (i : ℕ) :
    ∀ x : LowerCentralFactor G i, x^(m^(i+1)) ∈
      (intersectedFactorMap C (lowerSeries G i) (lowerSeries G (i+1))).range := by
  intro x
  let A := lowerSeries G i
  let B := lowerSeries G (i+1)
  let q := QuotientGroup.mk' (B.subgroupOf A)
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf A) x
  have hp := lowerSeries_power_coverage i m C hbase a.val a.property
  obtain ⟨c,hc,z,hz,he⟩ := Subgroup.mem_sup_of_normal_right.mp hp
  have hBA : B ≤ A := Subgroup.lowerCentralSeries_antitone ⊤ (Nat.le_succ i)
  have hcA : c ∈ A := by
    have h := A.mul_mem (A.pow_mem a.property (m^(i+1))) (A.inv_mem (hBA hz))
    rw [← he,mul_inv_cancel_right] at h
    exact h
  let ca : A := ⟨c,hcA⟩
  let za : A := ⟨z,hBA hz⟩
  have heq : ca*za = a^(m^(i+1)) := Subtype.ext he
  have hzq : q za = 1 := (QuotientGroup.eq_one_iff za).mpr hz
  refine ⟨QuotientGroup.mk' ((B.subgroupOf C).subgroupOf (A.subgroupOf C))
    (⟨⟨c,hc⟩,hcA⟩ : A.subgroupOf C),?_⟩
  change q ca = q a ^ (m^(i+1))
  rw [← map_pow,← heq,map_mul,hzq,mul_one]

/-- Cardinal comparison of one ambient central factor with its intersected
subgroup factor. -/
theorem lowerFactor_card_le_intersected_factor {G : Type*} [Group G] [Finite G]
    (C : Subgroup G) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ x : G, x^m ∈ C ⊔ commutator G) (i r : ℕ) (hr : Group.rank G ≤ r) :
    Nat.card (LowerCentralFactor G i) ≤
      Nat.card (SeriesFactor (fun j => (lowerSeries G j).subgroupOf C) i) *
        m^((i+1)*r^(i+1)) := by
  let F := LowerCentralFactor G i
  let J := SeriesFactor (fun j => (lowerSeries G j).subgroupOf C) i
  let f : J →* F := intersectedFactorMap C (lowerSeries G i) (lowerSeries G (i+1))
  let _ : CommGroup F := { (inferInstance : Group F) with mul_comm := mul_comm' }
  let Q := F ⧸ f.range
  let _ := Fintype.ofFinite Q
  have he : ∀ x : Q, x^(m^(i+1)) = 1 := by
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective f.range x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (lowerFactor_power_in_intersected_range C m hbase i a)
  have hcard := finite_abelian_card_le_exponent_rank (m^(i+1)) (pow_pos hm _) he
  have hrank : Group.rank Q ≤ r^(i+1) :=
    (Group.rank_le_of_surjective (QuotientGroup.mk' f.range) (QuotientGroup.mk'_surjective _)).trans
      ((lowerFactor_rank_bound G i).trans (Nat.pow_le_pow_left hr _))
  have hQ : Nat.card Q ≤ m^((i+1)*r^(i+1)) := by
    rw [Nat.card_eq_fintype_card]
    exact hcard.trans (by rw [pow_mul]; exact Nat.pow_le_pow_right (pow_pos hm _) hrank)
  have hJ : Nat.card f.range = Nat.card J :=
    (Nat.card_congr (MonoidHom.ofInjective (intersectedFactorMap_injective C _ _)).toEquiv).symm
  have horder := f.range.card_mul_index
  rw [Subgroup.index_eq_card,hJ] at horder
  rw [← horder]
  exact Nat.mul_le_mul_left _ hQ

end DirectedCycles
