import DirectedCycles.LocalApproximateSets
import DirectedCycles.LocalInternalFiniteRange
import DirectedCycles.LocalProductDomainTransfer
import DirectedCycles.LocalWordPowerTransfer

set_option autoImplicit false
open Filter
namespace DirectedCycles
variable {ι : Type*} (u : Ultrafilter ι) (G : ι → Type*)
    (L : ∀ i, LocalGroupAlgebra (G i)) (A : ∀ i, Set (G i))

/-- Local approximate groups with one uniform covering constant give an
actual local approximate set in the ultraproduct, with all product domains. -/
theorem localUltraSet_approximate {K : ℕ} (hK : 1 ≤ K)
    (hA : ∀ i, IsLocalApproximateSet (L i) K (A i)) :
    IsLocalApproximateSet (localUltraAlgebra (u : Filter ι) G L) K
      (localUltraSet (u : Filter ι) G A) := by
  classical
  let F : Filter ι := u
  let M := localUltraAlgebra F G L
  have h1 : M.one ∈ localUltraSet F G A :=
    (localUltraMk_mem_iff F G A _).2 (Eventually.of_forall fun i => (hA i).one_mem)
  refine ⟨hK,h1,?_,?_,?_⟩
  · intro x hx
    obtain ⟨a,rfl⟩ := Quotient.mk_surjective x
    apply (localUltraMk_mem_iff F G A _).2
    have ha := (localUltraMk_mem_iff F G A a).1 hx
    exact ha.mono fun i hi => (hA i).inv_mem (a i) hi
  · exact (localUltra_allProductsDefined_iff u G L A 200).2
      (Eventually.of_forall fun i => (hA i).allProducts)
  · choose X hcard hi hX3 hcover using fun i => (hA i).cover
    have hXnon : ∀ i, (X i).Nonempty := fun i => (hA i).nonempty_cover (hcover i)
    obtain ⟨E,hEcard,hE⟩ := localUltraSet_finite_of_bound u G X K hXnon hcard
    refine ⟨E,hEcard,?_,?_,?_⟩
    · intro x hx
      have hx' : x ∈ localUltraSet F G (fun i => (X i : Set (G i))) := hE ▸ hx
      obtain ⟨a,rfl⟩ := Quotient.mk_surjective x
      have ha := (localUltraMk_mem_iff F G _ a).1 hx'
      have hh : M.inv (localUltraMk F G a) ∈ localUltraSet F G (fun i => (X i : Set (G i))) :=
        (localUltraMk_mem_iff F G _ _).2 (ha.mono fun i hai => hi i (a i) hai)
      change M.inv (localUltraMk F G a) ∈ (E : Set _)
      rw [hE]
      exact hh
    · rw [hE,localUltra_wordPower u G L A 3]
      exact (localUltraSet_subset_iff_eventually u G (fun i => (L i).one) _ _).2
        (Eventually.of_forall hX3)
    · rw [hE,localUltra_wordPower u G L A 2,← localUltraSet_mul F G L]
      exact (localUltraSet_subset_iff_eventually u G (fun i => (L i).one) _ _).2
        (Eventually.of_forall hcover)
end DirectedCycles
