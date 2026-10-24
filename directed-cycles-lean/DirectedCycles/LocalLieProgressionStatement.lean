import DirectedCycles.LocalSmoothModelData
import DirectedCycles.LocalProgressionInductionProperty
import DirectedCycles.SmoothLocalExponentialChart

set_option autoImplicit false
open scoped Topology Manifold ContDiff
universe uι uG uH uE
namespace DirectedCycles

/-- The precise dimension-induction assertion. Its inputs are actual smooth
local model data and finite NSS approximate groups. Its conclusion gives
actual proper local nilprogressions with uniformly positive density and
diverging side lengths. This definition asserts no proof of the assertion. -/
def LocalLieProgressionStatement (d : ℕ) : Prop :=
  ∀ (ι : Type uι) (G : ι → Type uG) [∀ i, Fintype (G i)]
    (U : Ultrafilter ι) (L : ∀ i, LocalGroupAlgebra (G i)),
    (∀ i, (L i).DivisionClosed) → (∀ i, (L i).Reversible) →
  ∀ (H : Type uH) (E : Type uE) [TopologicalSpace H] [T2Space H] [LocallyCompactSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    [ChartedSpace E H] [IsManifold 𝓘(ℝ,E) ∞ H]
    (Q : LocalGroupAlgebra H),
    LocalGroupSmoothness (E := E) Q → Q.DivisionClosed → Q.Reversible →
  ∀ (A : ∀ i, Finset (G i)) (Ka : ℕ),
    (∀ᶠ i in (U : Filter ι), IsLocalFiniteApproximateGroup (L i) Ka (A i)) →
    (∀ᶠ i in (U : Filter ι), (L i).IsNSS (A i : Set (G i))) →
    LocalSmoothModelData U G L A Q → Module.finrank ℝ E = d →
    HasLargeLocalProgressions (U : Filter ι) G L (fun i => (A i : Set (G i)))
      (fun i => (A i).card)
end DirectedCycles
