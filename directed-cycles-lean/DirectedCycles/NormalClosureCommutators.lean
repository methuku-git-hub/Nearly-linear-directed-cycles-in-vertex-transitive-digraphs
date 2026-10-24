import DirectedCycles.RelativeCommutatorWeights

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- All commutators with one entry in a specified set. -/
def commutatorValues {G : Type*} [Group G] (S : Set G) : Set G :=
  {z | ∃ s ∈ S, ∃ g : G, ⁅s,g⁆ = z}

/-- Taking a normal closure commutes with forming commutators against the
whole ambient group. Thus no conjugate generators are silently omitted. -/
theorem normalClosure_commutatorValues {G : Type*} [Group G] (S : Set G) :
    Subgroup.normalClosure (commutatorValues S) =
      ⁅Subgroup.normalClosure S,(⊤ : Subgroup G)⁆ := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro z ⟨s,hs,g,rfl⟩
    exact Subgroup.commutator_mem_commutator (Subgroup.subset_normalClosure hs) (Subgroup.mem_top g)
  · let L := Subgroup.normalClosure (commutatorValues S)
    let q := QuotientGroup.mk' L
    have hq := QuotientGroup.mk'_surjective L
    have hs : q '' S ⊆ Subgroup.center (G ⧸ L) := by
      rintro z ⟨s,hs,rfl⟩
      apply Subgroup.mem_center_iff.mpr
      intro y
      obtain ⟨g,rfl⟩ := hq y
      apply Eq.symm
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr
        (Subgroup.subset_normalClosure (show ⁅s,g⁆ ∈ commutatorValues S from ⟨s,hs,g,rfl⟩))
    have hc : (Subgroup.normalClosure S).map q ≤ Subgroup.center (G ⧸ L) := by
      rw [Subgroup.map_normalClosure S q hq]
      exact Subgroup.normalClosure_le_normal hs
    have hz : (⁅Subgroup.normalClosure S,(⊤ : Subgroup G)⁆).map q = ⊥ := by
      rw [Subgroup.map_commutator,Subgroup.map_top_of_surjective q hq]
      exact Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hc
    have h := (Subgroup.map_eq_bot_iff _).mp hz
    rwa [QuotientGroup.ker_mk'] at h

/-- Values of left-nested commutators, with a first entry in S. -/
def iteratedCommutatorValues {G : Type*} [Group G] (S : Set G) : ℕ → Set G
  | 0 => S
  | n+1 => commutatorValues (iteratedCommutatorValues S n)

theorem normalClosure_iteratedCommutatorValues {G : Type*} [Group G] (S : Set G) (n : ℕ) :
    Subgroup.normalClosure (iteratedCommutatorValues S n) =
      relativeSeries (Subgroup.normalClosure S) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedCommutatorValues,normalClosure_commutatorValues,ih]
    rfl

/-- At a central term, ordinary generation and normal generation agree. -/
theorem closure_iteratedCommutatorValues_of_central {G : Type*} [Group G]
    (S : Set G) (n : ℕ)
    (hc : relativeSeries (Subgroup.normalClosure S) n ≤ Subgroup.center G) :
    Subgroup.closure (iteratedCommutatorValues S n) =
      relativeSeries (Subgroup.normalClosure S) n := by
  have hle : Subgroup.closure (iteratedCommutatorValues S n) ≤
      relativeSeries (Subgroup.normalClosure S) n := by
    rw [← normalClosure_iteratedCommutatorValues]
    exact Subgroup.closure_le_normalClosure
  have : (Subgroup.closure (iteratedCommutatorValues S n)).Normal :=
    Subgroup.normal_of_le_center (hle.trans hc)
  apply le_antisymm hle
  rw [← normalClosure_iteratedCommutatorValues]
  exact Subgroup.normalClosure_le_normal Subgroup.subset_closure

end DirectedCycles
