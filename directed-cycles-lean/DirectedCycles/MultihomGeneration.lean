module

public import DirectedCycles.GroupMultihomOperations

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles.GroupMultihom

/-- Separate homomorphisms extend subgroup membership from generating sets
in every variable. -/
theorem range_le_of_generating_sets {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ι → Type*} [∀ i, Group (B i)] {G : Type*} [Group G]
    (φ : GroupMultihom B G) (S : ∀ i, Set (B i))
    (hS : ∀ i, Subgroup.closure (S i) = ⊤) (H : Subgroup G)
    (hbase : ∀ x, (∀ i, x i ∈ S i) → φ x ∈ H) : Set.range φ ⊆ H := by
  classical
  have h : ∀ t : Finset ι, ∀ x, (∀ i, i ∉ t → x i ∈ S i) → φ x ∈ H := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro x hx
      exact hbase x (fun i => hx i (Finset.notMem_empty i))
    | @insert i t hi ih =>
      intro x hx
      let f := φ.slice x i
      have hf : Subgroup.closure (S i) ≤ H.comap f := by
        apply (H.comap f).closure_le.mpr
        intro a ha
        apply ih (Function.update x i a)
        intro j hj
        by_cases hji : j = i
        · subst j; simpa using ha
        · simpa [hji] using hx j (by simp [hji,hj])
      rw [hS i] at hf
      have hh := hf (Subgroup.mem_top (x i))
      simpa only [Subgroup.mem_comap,f,slice_apply_self] using hh
  rintro g ⟨x,rfl⟩
  exact h Finset.univ x (by simp)

theorem closure_range_eq_generated_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ι → Type*} [∀ i, Group (B i)] {G : Type*} [Group G]
    (φ : GroupMultihom B G) (S : ∀ i, Set (B i))
    (hS : ∀ i, Subgroup.closure (S i) = ⊤) :
    Subgroup.closure (Set.range φ) = Subgroup.closure (φ '' Set.pi Set.univ S) := by
  apply le_antisymm
  · apply (Subgroup.closure (φ '' Set.pi Set.univ S)).closure_le.mpr
    apply range_le_of_generating_sets φ S hS
    intro x hx
    exact Subgroup.subset_closure ⟨x,(fun i _ => hx i),rfl⟩
  · exact Subgroup.closure_mono (Set.image_subset_range _ _)

end DirectedCycles.GroupMultihom
