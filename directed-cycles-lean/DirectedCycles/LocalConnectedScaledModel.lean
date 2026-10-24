import DirectedCycles.LocalScaledModel
import DirectedCycles.LocalConnectedPowerSegments
import DirectedCycles.LocalMinimalEscapeUnbounded

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- In a connected nontrivial local model the least-escape scales are forced
to diverge. This supplies the nontrivial continuous curve without an additional
unbounded-scale hypothesis. -/
theorem local_connected_model_one_parameter {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [PreconnectedSpace H] [Nontrivial H]
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (hA : (localUltraAlgebra (U : Filter ι) G L).one ∈ localUltraSet (U : Filter ι) G A)
    (hdom : ∀ x ∈ localUltraSet (U : Filter ι) G A, ∀ y ∈ localUltraSet (U : Filter ι) G A,
      (localUltraAlgebra (U : Filter ι) G L).Defined x y)
    (hN : ∀ᶠ i in (U : Filter ι), 0 < N i)
    (hM : ∀ᶠ i in (U : Filter ι), 2*N i ≤ M i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (hexit : ∀ᶠ i in (U : Filter ι), (p i).power (N i) ∉ A i)
    (hnorm : ∀ᶠ i in (U : Filter ι), (L i).escapeNorm (A i) (u i) = 1/(N i : ℝ))
    (hmin : ∀ᶠ i in (U : Filter ι), ∀ v ∈ A i, v ≠ (L i).one →
      (L i).escapeNorm (A i) (u i) ≤ (L i).escapeNorm (A i) v)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hV : IsCompact V)
    (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ x ∈ localUltraSet (U : Filter ι) G A, π.toFun x ∈ V)
    (W : Set H) (hWo : IsOpen W) (hW1 : (1 : H) ∈ W)
    (hsmall : ∀ x, π.toFun x ∈ W → x ∈ localUltraSet (U : Filter ι) G A)
    (hthick : ∀ y ∈ W, ∃ x, π.toFun x = y) :
    ∃ φ : ℝ → H, Continuous φ ∧ φ 0 = 1 ∧
      (∀ s t : ℝ, φ (s+t) = φ s*φ t) ∧ φ 1 ≠ 1 ∧
      (∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u N M p t)) := by
  have hsegments := fun k => exists_local_long_power_segment_of_connected_model
    (localUltraAlgebra (U : Filter ι) G L) (localUltraSet (U : Filter ι) G A)
    hA hdom π W hWo hW1 hsmall hthick k
  have hunbounded := local_minimal_first_escape_unbounded U G L A u N hN hnorm hmin hsegments
  exact exists_local_scaled_one_parameter U G L hd hr A u N M p hunbounded hM hi hprev hexit
    π V hV hNSS himage W hW1 hsmall
end DirectedCycles
