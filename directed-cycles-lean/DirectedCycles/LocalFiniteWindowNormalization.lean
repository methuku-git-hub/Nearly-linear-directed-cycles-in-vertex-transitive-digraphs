import DirectedCycles.LocalSingletonWordWindow
import DirectedCycles.LocalInternalSetLogic

set_option autoImplicit false
namespace DirectedCycles

/-- Normalize exceptional component windows to the identity singleton.
Every finite hypothesis then holds at every index, while the internal source
set and all its model-image information remain exactly unchanged. -/
theorem local_finite_word_window_normalization {ι : Type*} (U : Ultrafilter ι)
    (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i)) (A B : ∀ i, Finset (G i))
    (hA1 : ∀ i, (L i).one ∈ A i) {K m : ℕ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ᶠ i in (U : Filter ι), IsLocalFiniteApproximateGroup (L i) K (B i) ∧ B i ⊆ A i ∧
      (L i).AllProductsDefined (B i : Set (G i)) m ∧
      ∀ n ≤ m, ∀ x ∈ (L i).wordPower (B i : Set (G i)) n, (L i).escapeNorm (A i : Set (G i)) x < ε) :
    ∃ B' : ∀ i, Finset (G i),
      (∀ᶠ i in (U : Filter ι), B' i = B i) ∧
      localUltraSet (U : Filter ι) G (fun i => (B' i : Set (G i))) =
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
      ∀ i, IsLocalFiniteApproximateGroup (L i) K (B' i) ∧ B' i ⊆ A i ∧
        (L i).AllProductsDefined (B' i : Set (G i)) m ∧
        ∀ n ≤ m, ∀ x ∈ (L i).wordPower (B' i : Set (G i)) n, (L i).escapeNorm (A i : Set (G i)) x < ε := by
  classical
  let Good := fun i (S : Finset (G i)) => IsLocalFiniteApproximateGroup (L i) K S ∧ S ⊆ A i ∧
    (L i).AllProductsDefined (S : Set (G i)) m ∧
    ∀ n ≤ m, ∀ x ∈ (L i).wordPower (S : Set (G i)) n, (L i).escapeNorm (A i : Set (G i)) x < ε
  have hone : ∀ i, Good i {(L i).one} := by
    intro i
    refine ⟨local_singleton_one_approximate (L i) hK,?_,?_,?_⟩
    · exact Finset.singleton_subset_iff.mpr (hA1 i)
    · simpa only [Finset.coe_singleton] using (L i).allProductsDefined_singleton_one m
    · intro n _ x hx
      have he : x = (L i).one := by
        simpa only [Finset.coe_singleton,(L i).wordPower_singleton_one,Set.mem_singleton_iff] using hx
      rw [he,(L i).escapeNorm_one (hA1 i)]
      exact hε
  let B' : ∀ i, Finset (G i) := fun i => if Good i (B i) then B i else {(L i).one}
  have he : ∀ᶠ i in (U : Filter ι), B' i = B i :=
    hgood.mono fun i hi => by dsimp only [B']; rw [ite_eq_left hi]
  refine ⟨B',he,?_,?_⟩
  · exact (localUltraSet_eq_iff_eventually U G (fun i => (L i).one) _ _).2
      (he.mono fun i hi => congrArg (fun S : Finset (G i) => (S : Set (G i))) hi)
  · intro i
    dsimp only [B']
    split_ifs with hi
    · exact hi
    · exact hone i
end DirectedCycles
