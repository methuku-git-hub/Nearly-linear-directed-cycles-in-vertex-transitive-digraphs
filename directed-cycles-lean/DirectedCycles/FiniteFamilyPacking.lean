module

public import DirectedCycles.FiniteFamilyOverlap

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace FiniteAlmostPeriods
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- A maximal disjoint subfamily meets every member of a finite family.
The packing bound follows from the disjoint union, with no group structure. -/
theorem finite_family_packing (I : Finset α) (R : Finset β) (T : α → Finset β)
    (m : ℕ) (hm : 0 < m) (hTR : ∀ a ∈ I, T a ⊆ R)
    (hsize : ∀ a ∈ I, (T a).card = m) :
    ∃ X : Finset α, X ⊆ I ∧ X.card*m ≤ R.card ∧
      ∀ a ∈ I, ∃ x ∈ X, (T a ∩ T x).Nonempty := by
  classical
  let F := I.powerset.filter (fun (X : Finset α) => (X : Set α).PairwiseDisjoint T)
  have hempty : (∅ : Finset α) ∈ F := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.empty_subset I),?_⟩
    intro a ha
    exact (Finset.notMem_empty a ha).elim
  obtain ⟨X,hX,hmax⟩ := F.exists_max_image Finset.card ⟨∅,hempty⟩
  obtain ⟨hXI,hdisj⟩ := Finset.mem_filter.mp hX
  have hXI' := Finset.mem_powerset.mp hXI
  refine ⟨X,hXI',?_,?_⟩
  · have hU : X.biUnion T ⊆ R := by
      intro z hz
      obtain ⟨a,ha,hz⟩ := Finset.mem_biUnion.mp hz
      exact hTR a (hXI' ha) hz
    calc
      X.card*m = ∑ a ∈ X, (T a).card := by
        rw [Finset.sum_congr rfl (fun a ha => hsize a (hXI' ha))]
        simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
      _ = (X.biUnion T).card := (Finset.card_biUnion hdisj).symm
      _ ≤ R.card := Finset.card_le_card hU
  · intro a ha
    by_contra hn
    have haX : a ∉ X := by
      intro haX
      have hne : (T a).Nonempty := Finset.card_pos.mp (by rw [hsize a ha]; exact hm)
      apply hn
      exact ⟨a,haX,by simpa only [Finset.inter_self] using hne⟩
    have hpair : (↑(insert a X) : Set α).PairwiseDisjoint T := by
      rw [Finset.coe_insert]
      apply hdisj.insert
      intro x hx _
      apply Finset.disjoint_left.mpr
      intro z hza hzx
      exact hn ⟨x,hx,⟨z,Finset.mem_inter.mpr ⟨hza,hzx⟩⟩⟩
    have hnew : insert a X ∈ F := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.insert_subset ha hXI'),hpair⟩
    have hh := hmax (insert a X) hnew
    rw [Finset.card_insert_of_notMem haX] at hh
    omega
end FiniteAlmostPeriods
end DirectedCycles
