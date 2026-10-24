import DirectedCycles.FunctionalCycles
import DirectedCycles.LayerCycleLength
import DirectedCycles.LayerEquivalence
import DirectedCycles.RoundCycleExpansion

set_option autoImplicit false
namespace DirectedCycles

/-- With a singleton coordinate group, a strongly connected layer graph has
a Hamiltonian cycle, and consequently every coordinate in every layer. -/
theorem subsingleton_layer_hamiltonian {G : Type*} [Group G] [Subsingleton G]
    {T : ℕ} (hT : 2 ≤ T) (S : ZMod T → Set G)
    (hsc : StronglyConnected (CyclicLayerDigraph S)) :
    ∃ C : Cycle (CyclicLayerDigraph S), T ≤ C.length ∧ Function.Surjective C.vertex := by
  obtain ⟨C,hC⟩ := stronglyConnected_layer_cycle hT S hsc
  refine ⟨C,hC,C.surjective_of_functional_strong ?_ hsc⟩
  rintro x y z ⟨hy,_,_,_⟩ ⟨hz,_,_,_⟩
  exact Prod.ext (Subsingleton.elim _ _) (hy.trans hz.symm)

/-- The lower-class layer input is proved outright for the trivial group. -/
theorem subsingleton_layer_lower_bound {G : Type*} [Group G] [Subsingleton G] (eta : ℝ) :
    LayerCycleLowerBound G 1 eta := by
  intro T hT S _ hsc
  obtain ⟨C,hC,_⟩ := subsingleton_layer_hamiltonian hT S hsc
  refine ⟨C,?_⟩
  have hcard : Nat.card G = 1 := Nat.card_unique
  simpa only [hcard,Nat.cast_one,Real.one_rpow,one_mul,mul_one] using (show (T : ℝ) ≤ C.length by exact_mod_cast hC)

end DirectedCycles
