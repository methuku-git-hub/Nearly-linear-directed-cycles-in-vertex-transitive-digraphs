module

public import DirectedCycles.GeneratorCommutatorNilpotence

@[expose] public section

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- Iterated commutators associated to the left, with a designated first
letter and an explicit list of subsequent generator indices. -/
def leftGeneratorCommutator {α G : Type*} [Group G] (g : α → G) (i : α) (l : List α) : G :=
  l.foldl (fun x j => ⁅x,g j⁆) (g i)

theorem leftGeneratorCommutator_append {α G : Type*} [Group G] (g : α → G) (i : α) (l : List α) (j : α) :
    leftGeneratorCommutator g i (l++[j]) = ⁅leftGeneratorCommutator g i l,g j⁆ := by
  simp only [leftGeneratorCommutator,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem iteratedGeneratorCommutators_left_words {α G : Type*} [Group G] (g : α → G) (n : ℕ) :
    iteratedGeneratorCommutators (Set.range g) n ⊆
      {x | ∃ i : α, ∃ l : List α, l.length = n ∧ leftGeneratorCommutator g i l = x} := by
  induction n with
  | zero =>
    rintro _ ⟨i,rfl⟩
    exact ⟨i,[],rfl,rfl⟩
  | succ n ih =>
    rintro _ ⟨x,hx,y,⟨j,rfl⟩,rfl⟩
    obtain ⟨i,l,hl,rfl⟩ := ih hx
    exact ⟨i,l++[j],by simp only [List.length_append,List.length_cons,List.length_nil,hl],
      leftGeneratorCommutator_append g i l j⟩

/-- Nilpotence needs only the left-associated generator identities. This
avoids an unnecessary local Hall-Witt reduction; the global lower-central
series proof supplies all other commutator identities. -/
theorem nilpotent_of_left_generator_commutators {α G : Type*} [Group G]
    (g : α → G) (hgen : Subgroup.closure (Set.range g) = ⊤) (c : ℕ)
    (hwords : ∀ i : α, ∀ l : List α, l.length = c → leftGeneratorCommutator g i l = 1) :
    ∃ _hNil : Group.IsNilpotent G, Group.nilpotencyClass G ≤ c := by
  have hv : iteratedGeneratorCommutators (Set.range g) c ⊆ ({1} : Set G) := by
    intro x hx
    obtain ⟨i,l,hl,rfl⟩ := iteratedGeneratorCommutators_left_words g c hx
    exact hwords i l hl
  have hbot : lowerSeries G c = ⊥ := by
    rw [← normalClosure_iteratedGeneratorCommutators (Set.range g) hgen c]
    exact Subgroup.normalClosure_eq_bot_iff.mpr hv
  have hnil : Group.IsNilpotent G := Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨c,hbot⟩
  exact ⟨hnil,Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hbot⟩
end DirectedCycles
