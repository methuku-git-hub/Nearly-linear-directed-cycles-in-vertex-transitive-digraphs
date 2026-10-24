import DirectedCycles.LocalTrivialModel
import DirectedCycles.ConnectedZeroDimensionalManifold
import DirectedCycles.GlobalProgressionDensity

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- The zero-dimensional connected model closes the actual progression
induction base: the finite windows have rank-zero, step-zero witnesses
and density factor one on an ultrafilter-large set. -/
theorem local_zero_dimensional_progression {ι H E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [ChartedSpace E H] [PreconnectedSpace H]
    (hdim : Module.finrank ℝ E = 0)
    (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (M : LocalGroupAlgebra H) (A : ∀ i, Finset (G i)) {K : ℕ}
    (hA : ∀ i, IsLocalFiniteApproximateGroup (L i) K (A i))
    (hNSS : ∀ i, (L i).IsNSS (A i : Set (G i)))
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) M)
    (hkernel : ∀ z, π.toFun z = M.one →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))) :
    ∀ᶠ i in (U : Filter ι), ∃ W : (L i).ProgressionWitness (A i : Set (G i)) 0 0,
      (A i).card ≤ 1 * ∏ j, (2*W.lengths j+1) := by
  classical
  let : Subsingleton H := connected_manifold_subsingleton_of_finrank_zero (E := E) hdim
  have hh := local_trivial_model_eventually_singleton U G L M A hA hNSS π hkernel
  filter_upwards [hh] with i hi
  have W : (L i).ProgressionWitness (A i : Set (G i)) 0 0 :=
    hi.symm ▸ (L i).identityProgressionWitness
  refine ⟨W,?_⟩
  have he : A i = {(L i).one} := by
    apply Finset.coe_injective
    simpa only [Finset.coe_singleton] using hi
  simp only [Fin.prod_univ_zero,one_mul,he,Finset.card_singleton,le_refl]

/-- The invariant has an exact finite-global exit into the downstream
coset-nilprogression statement. -/
theorem global_progression_of_witness {G : Type*} [Group G] [Finite G]
    {A : Set G} {r c : ℕ} (W : (LocalGroupAlgebra.ofGroup G).ProgressionWitness A r c)
    (a J : ℕ) (hdensity : a ≤ J * ∏ i, (2*W.lengths i+1)) :
    ∃ P : CosetNilprogression G r c, P.carrier ⊆ A ∧ a ≤ J*Nat.card P.carrier :=
  global_progression_of_local_data W.generators W.lengths W.lengths_pos A W.words W.proper W.commutators a J hdensity
end DirectedCycles
