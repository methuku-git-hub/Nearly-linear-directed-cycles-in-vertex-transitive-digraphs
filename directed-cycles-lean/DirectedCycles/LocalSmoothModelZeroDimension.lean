module

public import DirectedCycles.LocalSmoothModelStrongWindows
public import DirectedCycles.LocalTrivialInternalModel
public import DirectedCycles.LocalProgressionInductionProperty
public import DirectedCycles.SmoothLocalExponentialChart

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles.LocalSmoothModelData

/-- The zero-dimensional induction base uses a small coordinate window.
No connectedness of the local target is required. -/
theorem zero_dimension {ι H E : Type*}
    [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [ChartedSpace E H]
    [IsManifold 𝓘(ℝ,E) ∞ H]
    {U : Ultrafilter ι} {G : ι → Type*} [∀ i, Fintype (G i)]
    {L : ∀ i, LocalGroupAlgebra (G i)} {A : ∀ i, Finset (G i)}
    {Q : LocalGroupAlgebra H} (M : LocalSmoothModelData U G L A Q)
    (hQ : LocalGroupSmoothness (E := E) Q)
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    {Ka : ℕ} (hA : ∀ᶠ i in (U : Filter ι), IsLocalFiniteApproximateGroup (L i) Ka (A i))
    (hNSS : ∀ᶠ i in (U : Filter ι), (L i).IsNSS (A i : Set (G i)))
    (hdim : Module.finrank ℝ E = 0) :
    HasLargeLocalProgressions (U : Filter ι) G L (fun i => (A i : Set (G i)))
      (fun i => (A i).card) := by
  classical
  let : Subsingleton E := (Module.finrank_eq_zero_iff_of_free ℝ E).1 hdim
  obtain ⟨D⟩ := smooth_local_exponential_data Q hQ
  obtain ⟨K,R,_hK,hR,hwin⟩ := M.large_strong_windows D hQ hd hr hA
  obtain ⟨B,J,hJ,hBin,hBout,hgood⟩ := hwin (R/2) (by positivity) (by linarith)
  have hB : ∀ᶠ i in (U : Filter ι), IsLocalFiniteApproximateGroup (L i) K (B i) :=
    hgood.mono fun _ h => h.2.2.approximate
  have hBNSS : ∀ᶠ i in (U : Filter ι), (L i).IsNSS (B i : Set (G i)) := by
    filter_upwards [hgood,hNSS] with i hi hn
    exact fun S hS hSB => hn S hS (hSB.trans hi.1)
  have hsingle := local_trivial_internal_model_eventually_singleton U G L Q B hB hBNSS M.map
    (by
      intro z hz
      obtain ⟨v,_hv,hv⟩ := hBout hz
      rw [Subsingleton.elim v 0,D.zero] at hv
      exact hv.symm)
    (by
      intro z hz
      apply hBin
      exact ⟨0,by simpa only [Metric.mem_closedBall,dist_self] using (by positivity : (0 : ℝ) ≤ R/2),
        D.zero.trans hz.symm⟩)
  apply HasLargeLocalProgressions.of_bounded_card (hA.mono fun _ h => h.one_mem) hJ
  filter_upwards [hgood,hsingle] with i hi hsi
  have he : B i = {(L i).one} := by
    apply Finset.coe_injective
    simpa only [Finset.coe_singleton] using hsi
  simpa only [he,Finset.card_singleton,Nat.mul_one] using hi.2.1
end DirectedCycles.LocalSmoothModelData
