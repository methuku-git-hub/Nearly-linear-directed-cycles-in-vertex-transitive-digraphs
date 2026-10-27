module

public import DirectedCycles.CosetNilprogression
public import Mathlib.Combinatorics.Additive.ApproximateSubgroup

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

theorem no_commutator_word_fin_zero (w : CommutatorWord (Fin 0)) : False := by
  induction w with
  | var i => exact Fin.elim0 i
  | bracket a b ha hb => exact ha

/-- An actual subgroup is a rank-zero, step-zero coset nilprogression. -/
noncomputable def subgroupCosetNilprogression {G : Type*} [Group G] (H : Subgroup G) :
    CosetNilprogression G 0 0 where
  U := H
  H := H
  hHU := le_refl H
  normal := by simp only [Subgroup.subgroupOf_self]; infer_instance
  generators := Fin.elim0
  lengths := Fin.elim0
  lengths_pos i := Fin.elim0 i
  generates := by simp only [Subgroup.subgroupOf_self,Subgroup.coe_top,Set.univ_union,Subgroup.closure_univ]
  commutators := by
    intro w _
    exact (no_commutator_word_fin_zero w).elim

theorem subgroupCosetNilprogression_carrier {G : Type*} [Group G] (H : Subgroup G) :
    (subgroupCosetNilprogression H).carrier = (H : Set G) :=
  Set.Subset.antisymm (subgroupCosetNilprogression H).carrier_subset_U
    (subgroupCosetNilprogression H).subgroup_subset_carrier

/-- The finite coset-cover bound is exactly the size bound required for the
rank-zero coset nilprogression, with no hidden index assumption. -/
theorem rank_zero_card_bound_of_cover {G : Type*} [Group G] [Fintype G]
    (A E : Finset G) (H : Subgroup G)
    (hcover : (A : Set G) ⊆ (E : Set G)*(H : Set G)) :
    Nat.card (A : Set G) ≤ E.card*Nat.card (subgroupCosetNilprogression H).carrier := by
  classical
  let R := (H : Set G).toFinset
  have hcov : A ⊆ E*R := by
    intro a ha
    have hh := hcover ha
    obtain ⟨e,he,h,hh,rfl⟩ := hh
    exact Finset.mem_mul.mpr ⟨e,he,h,by simpa only [R,Set.mem_toFinset] using hh,rfl⟩
  have hcard : A.card ≤ E.card*R.card := (Finset.card_le_card hcov).trans Finset.card_mul_le
  have hR : R.card = Nat.card (H : Set G) := (Nat.card_eq_card_toFinset _).symm
  rw [subgroupCosetNilprogression_carrier,Nat.card_coe_set_eq,Set.ncard_coe_finset]
  simpa only [hR] using hcard
end DirectedCycles
