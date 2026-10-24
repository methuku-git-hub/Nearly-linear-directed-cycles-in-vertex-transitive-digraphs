import DirectedCycles.LocalTrivialModel
import DirectedCycles.LocalInternalSubgroups
import DirectedCycles.LocalUltraproductProducts
import DirectedCycles.LocalProductDomainTransfer
import DirectedCycles.LocalApproximateFiniteTransfer

set_option autoImplicit false
namespace DirectedCycles

/-- An internal source lying in the actual model kernel is eventually the
identity singleton when its finite components are NSS. The target itself
need not be trivial or connected. -/
theorem local_trivial_internal_model_eventually_singleton {ι H : Type*}
    (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (Q : LocalGroupAlgebra H) (A : ∀ i, Finset (G i)) {K : ℕ}
    (hA : ∀ᶠ i in (U : Filter ι), IsLocalFiniteApproximateGroup (L i) K (A i))
    (hNSS : ∀ᶠ i in (U : Filter ι), (L i).IsNSS (A i : Set (G i)))
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z = Q.one)
    (hkernel : ∀ z, π.toFun z = Q.one →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))) :
    ∀ᶠ i in (U : Filter ι), (A i : Set (G i)) = {(L i).one} := by
  let J := localUltraAlgebra (U : Filter ι) G L
  let S := localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))
  have hS1 : J.one ∈ S := (localUltraMk_mem_iff (U : Filter ι) G _ _).2 (hA.mono fun _ h => h.one_mem)
  have hSi : ∀ x ∈ S, J.inv x ∈ S :=
    (localUltra_inv_closed_iff U G L _).2 (hA.mono fun _ h => h.inv_mem)
  have hdom : J.AllProductsDefined S 2 := (localUltra_allProductsDefined_iff U G L _ 2).2
    (hA.mono fun i h => h.allProducts.mono (L i) (Set.Subset.refl _) (by omega : 2 ≤ 200))
  have hgroup : J.IsGlobalSubgroup S := by
    refine ⟨hS1,hSi,?_⟩
    intro x hx y hy
    obtain ⟨z,hz⟩ := hdom [x,y] (by simp) (by
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl
      · exact hx
      · exact hy)
    have hxy := (LocalGroupAlgebra.Product.pair_iff J x y z).1 hz
    refine ⟨z,hkernel z ?_,hxy⟩
    have hh := π.map_mul hxy
    rw [himage x hx,himage y hy] at hh
    exact Q.unique hh (Q.one_mul Q.one)
  have hcomp := (localUltraSet_isGlobalSubgroup_iff G L U (fun i => (A i : Set (G i)))).1 hgroup
  filter_upwards [hA,hNSS,hcomp] with i hai hnssi hgi
  exact Set.Subset.antisymm (hnssi _ hgi (Set.Subset.refl _))
    (Set.singleton_subset_iff.mpr hai.one_mem)
end DirectedCycles
