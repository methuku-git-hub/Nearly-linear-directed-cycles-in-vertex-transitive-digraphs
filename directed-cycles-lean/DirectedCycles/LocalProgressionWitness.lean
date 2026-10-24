import DirectedCycles.LocalOrderedGrid
import DirectedCycles.LocalIteratedGeneratorCommutators
import DirectedCycles.LocalOrderedGridRestriction

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*}

/-- The induction invariant uses actual signed-word domains and proper
ordered coordinates. Nilpotence is stated by ambient local commutators;
no upper-triangular normal form is built into the invariant. -/
structure ProgressionWitness (L : LocalGroupAlgebra G) (A : Set G) (r c : ℕ) where
  generators : Fin r → G
  lengths : Fin r → ℕ
  lengths_pos : ∀ i, 1 ≤ lengths i
  words : L.SignedWordsIn generators lengths A
  proper : Function.Injective (L.orderedGrid words)
  commutators : ∀ x, L.GeneratorCommutators (Set.range generators) c x → x = L.one

/-- Package proved word data into the induction invariant, retaining the
literal supplied coordinate lengths. -/
theorem exists_progressionWitness_of_data (L : LocalGroupAlgebra G) (A : Set G) {r c : ℕ}
    (g : Fin r → G) (N : Fin r → ℕ) (hN : ∀ i, 1 ≤ N i)
    (hw : L.SignedWordsIn g N A) (hproper : Function.Injective (L.orderedGrid hw))
    (hc : ∀ x, L.GeneratorCommutators (Set.range g) c x → x = L.one) :
    ∃ W : L.ProgressionWitness A r c, W.lengths = N :=
  ⟨⟨g,N,hN,hw,hproper,hc⟩,rfl⟩

/-- Enlarging the containing window retains the same actual progression. -/
noncomputable def ProgressionWitness.mono {L : LocalGroupAlgebra G} {A B : Set G} {r c : ℕ}
    (W : L.ProgressionWitness A r c) (hAB : A ⊆ B) : L.ProgressionWitness B r c := by
  have hw := W.words.mono L (fun _ => le_rfl) hAB
  exact ⟨W.generators,W.lengths,W.lengths_pos,hw,
    L.orderedGrid_injective_change_set hw W.words W.proper,W.commutators⟩

/-- The zero-rank invariant is constructed directly in the identity set. -/
noncomputable def identityProgressionWitness (L : LocalGroupAlgebra G) :
    L.ProgressionWitness {L.one} 0 0 := by
  let g : Fin 0 → G := Fin.elim0
  let N : Fin 0 → ℕ := Fin.elim0
  have hw : L.SignedWordsIn g N {L.one} := by
    intro w _
    have he : w = [] := List.eq_nil_iff_forall_not_mem.mpr (fun a _ => Fin.elim0 a.1)
    subst w
    exact ⟨L.one,rfl,Product.nil⟩
  refine ⟨g,N,fun i => Fin.elim0 i,hw,?_,?_⟩
  · intro k l _
    funext i
    exact Fin.elim0 i
  · intro x hx
    cases hx with
    | base hx =>
      obtain ⟨i,_⟩ := hx
      exact Fin.elim0 i
end LocalGroupAlgebra
end DirectedCycles
