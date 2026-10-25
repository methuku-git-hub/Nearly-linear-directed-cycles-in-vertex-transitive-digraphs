module

public import DirectedCycles.StrongLocalUniformNSSQuotient
public import DirectedCycles.LocalApproximateUltra
public import DirectedCycles.LocalInternalSubgroups

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Uniform finite local NSS reduction gives actual internal approximate
sets in the component quotient ultraproduct. Its NSS assertion excludes
internal global subgroups, as required in the nonstandard argument. The
subgroup removed is the internal set of exact component zero-escape
elements, not the larger external zero set of the real limiting norm. -/
theorem strong_local_internal_nss_quotient (K : ℕ) (hK : 1 ≤ K) :
    ∃ (J : ℕ) (δ : ℝ), 1 ≤ J ∧ 0 < δ ∧
      ∀ (ι : Type*) (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Fintype (G i)]
        (L : ∀ i, LocalGroupAlgebra (G i)) (hd : ∀ i, (L i).DivisionClosed)
        (hr : ∀ i, (L i).Reversible) (A : ∀ i, Finset (G i)),
      (∀ i, IsStrongLocalFiniteApproximateGroup (L i) K (A i)) →
      let H := fun i => {x | (L i).escapeNorm (A i) x = 0}
      ∃ B : ∀ i, Finset (G i),
        (∀ i, IsLocalFiniteApproximateGroup (L i) J (B i) ∧
          δ*(A i).card ≤ (B i).card ∧ (L i).wordPower (B i : Set (G i)) 200 ⊆ (A i : Set (G i))) ∧
        ∃ W : ∀ i, (L i).NormalSubgroupWindow (H i) ((L i).setMul (H i) (A i)),
          let QG := fun i => ((W i).congruence (hd i) (hr i)).Carrier
          let QL := fun i => ((W i).congruence (hd i) (hr i)).algebra
          let Q := fun i => (W i).finiteImage (hd i) (hr i) (B i)
          IsLocalApproximateSet (localUltraAlgebra (U : Filter ι) QG QL) J
            (localUltraSet (U : Filter ι) QG (fun i => (Q i : Set (QG i)))) ∧
          LocalInternalNSS QG QL U (fun i => (Q i : Set (QG i))) ∧
          (localUltraAlgebra (U : Filter ι) G L).IsGlobalSubgroup (localUltraSet (U : Filter ι) G H) ∧
          (∀ i, δ*(A i).card ≤ (Q i).card*((localZeroEscapeFinset (L i) (A i)).card : ℝ)) := by
  classical
  obtain ⟨J,δ,hJ,hδ,hfinite⟩ := strong_local_uniform_nss_quotient K hK
  refine ⟨J,δ,hJ,hδ,?_⟩
  intro ι U G _ L hd hr A hA
  dsimp only
  have hex := fun i => hfinite (G i) (L i) (hd i) (hr i) (A i) (hA i)
  choose B hB hBd hBsmall W hQ hNSS hD hR hcard using hex
  refine ⟨B,(fun i => ⟨hB i,hBd i,hBsmall i⟩),W,?_,?_,?_,hcard⟩
  · exact localUltraSet_approximate U _ _ _ hJ (fun i => localApproximateSet_finset_iff.mpr (hQ i))
  · apply local_internal_nss_of_components
    exact Filter.Eventually.of_forall fun i S hS _ => hNSS i S hS (Set.subset_univ S)
  · exact localUltraSet_isGlobalSubgroup (U : Filter ι) G L _
      (Filter.Eventually.of_forall fun i => (W i).subgroup)
end DirectedCycles
