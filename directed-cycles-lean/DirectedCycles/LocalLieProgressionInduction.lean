module

public import DirectedCycles.LocalNormalizedProgressionStep
public import DirectedCycles.LocalSmoothModelZeroDimension

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Topology Manifold ContDiff
universe uι uG uH uE
namespace DirectedCycles

/-- Full well-founded Lie-dimension induction for actual smooth local
models of finite NSS approximate groups. The lower-dimensional targets
remain local, so no globalization assertion is needed. -/
theorem local_lie_progression_induction (d : ℕ) :
    LocalLieProgressionStatement.{uι,uG,uH,uE} d := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro ι G instG U L hd hr H E topH t2H lcH naddE nsE fdE compE charts man Q hQ hdQ hrQ A Ka hA hNSS M hdim
    by_cases hz : Module.finrank ℝ E = 0
    · exact M.zero_dimension hQ hd hr hA hNSS hz
    let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
    obtain ⟨Y⟩ := smooth_local_exponential_data Q hQ
    obtain ⟨K,J,_hK,hJ,B,hgood,Mb,hnormal⟩ := M.exists_normalized_window Y hQ hd hr hA
    by_cases hne : ∀ᶠ i in (U : Filter ι), ∃ g ∈ B i, g ≠ (L i).one
    · let s : Set ι := {i | IsStrongLocalFiniteApproximateGroup (L i) K (B i) ∧
        (L i).IsNSS (B i : Set (G i)) ∧ ∃ g ∈ B i, g ≠ (L i).one}
      have hs : s ∈ U := by
        filter_upwards [hgood,hNSS,hne] with i hi hn hni
        exact ⟨hi.2.2,(fun S hS hSB => hn S hS (hSB.trans hi.1)),hni⟩
      have hrestricted := local_normalized_progression_step
        (U := localLargeIndexUltrafilter U s hs)
        (G := fun j : s => G j.val) (L := fun j : s => L j.val)
        (fun j => hd j.val) (fun j => hr j.val) Y hQ hdQ hrQ
        (fun j => j.property.1) (fun j => j.property.2.1) (fun j => j.property.2.2)
        (Mb.restrict s hs) (hnormal.restrict s hs)
        (fun d' hd' => ih d' (by omega))
      have hB : HasLargeLocalProgressions (U : Filter ι) G L
          (fun i => (B i : Set (G i))) (fun i => (B i).card) :=
        HasLargeLocalProgressions.of_largeIndex U s hs hrestricted
      exact hB.of_containment_density hJ (hgood.mono fun _ hi => hi.1)
        (hgood.mono fun _ hi => hi.2.1)
    · apply HasLargeLocalProgressions.of_bounded_card (hA.mono fun _ hi => hi.one_mem) hJ
      filter_upwards [hgood,Ultrafilter.eventually_not.mpr hne] with i hi hni
      have hsub : B i ⊆ {(L i).one} := by
        intro g hg
        apply Finset.mem_singleton.mpr
        by_contra hneq
        exact hni ⟨g,hg,hneq⟩
      have hcard : (B i).card ≤ 1 := by
        simpa only [Finset.card_singleton] using Finset.card_le_card hsub
      exact hi.2.1.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left J hcard)
end DirectedCycles
