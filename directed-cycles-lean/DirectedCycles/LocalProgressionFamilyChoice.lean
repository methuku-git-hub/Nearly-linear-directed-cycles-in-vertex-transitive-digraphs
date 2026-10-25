module

public import DirectedCycles.LocalProgressionWitness

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} {L : LocalGroupAlgebra G} {A : Set G} {r c : ℕ}

/-- Retain a prescribed length function when exposing a progression
witness as the tuple and word data required by the induction step. -/
theorem ProgressionWitness.tuple_data (W : L.ProgressionWitness A r c) (N : Fin r → ℕ)
    (hN : W.lengths = N) :
    ∃ hw : L.SignedWordsIn W.generators N A, Function.Injective (L.orderedGrid hw) ∧
      (∀ x, L.GeneratorCommutators (Set.range W.generators) c x → x = L.one) := by
  subst N
  exact ⟨W.words,W.proper,W.commutators⟩
end LocalGroupAlgebra

/-- Choose actual generator tuples from eventual witnesses. Exceptional
components use the identity tuple and make no asserted progression claim;
the original fixed length functions and their divergence are retained. -/
theorem choose_local_progression_family {ι : Type*} (F : Filter ι)
    (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i)) (A : ∀ i, Set (G i))
    {r c J : ℕ} (N : ι → Fin r → ℕ) (a : ι → ℕ)
    (hW : ∀ᶠ i in F, ∃ W : (L i).ProgressionWitness (A i) r c,
      W.lengths = N i ∧ a i ≤ J*∏ j, (2*W.lengths j+1)) :
    ∃ g : ∀ i, Fin r → G i, ∀ᶠ i in F,
      ∃ hw : (L i).SignedWordsIn (g i) (N i) (A i),
        Function.Injective ((L i).orderedGrid hw) ∧
        (∀ x, (L i).GeneratorCommutators (Set.range (g i)) c x → x = (L i).one) ∧
        a i ≤ J*∏ j, (2*N i j+1) := by
  classical
  let Q : ι → Prop := fun i => ∃ W : (L i).ProgressionWitness (A i) r c,
    W.lengths = N i ∧ a i ≤ J*∏ j, (2*W.lengths j+1)
  let g : ∀ i, Fin r → G i := fun i => if h : Q i then (Classical.choose h).generators else fun _ => (L i).one
  refine ⟨g,?_⟩
  filter_upwards [hW] with i hi
  have hNi := (Classical.choose_spec hi).1
  have hcard := (Classical.choose_spec hi).2
  rw [hNi] at hcard
  obtain ⟨hw,hproper,hcomm⟩ := (Classical.choose hi).tuple_data (N i) hNi
  have hg : g i = (Classical.choose hi).generators := by
    dsimp only [g]
    rw [dite_eq_left hi]
  rw [hg]
  exact ⟨hw,hproper,hcomm,hcard⟩
end DirectedCycles
