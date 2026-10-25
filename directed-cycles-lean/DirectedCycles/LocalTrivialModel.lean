module

public import DirectedCycles.LocalApproximateGroups
public import DirectedCycles.LocalGlobalSubgroup
public import DirectedCycles.LocalInternalSetLogic
public import DirectedCycles.LocalProgressionWitness

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A trivial target and the actual model-kernel inclusion force finite
NSS source windows to be the identity set on an ultrafilter-large set. -/
theorem local_trivial_model_eventually_singleton {ι H : Type*} [Subsingleton H]
    (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (M : LocalGroupAlgebra H) (A : ∀ i, Finset (G i)) {K : ℕ}
    (hA : ∀ i, IsLocalFiniteApproximateGroup (L i) K (A i))
    (hNSS : ∀ i, (L i).IsNSS (A i : Set (G i)))
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) M)
    (hkernel : ∀ z, π.toFun z = M.one →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))) :
    ∀ᶠ i in (U : Filter ι), (A i : Set (G i)) = {(L i).one} := by
  have hfull : ∀ᶠ i in (U : Filter ι), (Set.univ : Set (G i)) ⊆ A i := by
    apply (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) (fun _ => Set.univ) _).1
    intro z _
    exact hkernel z (Subsingleton.elim _ _)
  filter_upwards [hfull] with i hi
  have hgroup : (L i).IsGlobalSubgroup Set.univ := by
    refine ⟨Set.mem_univ _,fun _ _ => Set.mem_univ _,?_⟩
    intro x _ y _
    obtain ⟨z,hz⟩ := (hA i).allProducts [x,y] (by simp) (by
      intro a _
      exact hi (Set.mem_univ a))
    exact ⟨z,Set.mem_univ _,(LocalGroupAlgebra.Product.pair_iff (L i) x y z).1 hz⟩
  apply Set.Subset.antisymm
  · intro x _
    exact hNSS i Set.univ hgroup hi (Set.mem_univ x)
  · exact Set.singleton_subset_iff.mpr (hA i).one_mem
end DirectedCycles
