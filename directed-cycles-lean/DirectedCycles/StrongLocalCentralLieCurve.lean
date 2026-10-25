module

public import DirectedCycles.StrongLocalCentralCurve
public import DirectedCycles.LieOneParameterSmooth
public import DirectedCycles.LieOneParameterNonzero

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {H E : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [PreconnectedSpace H] [Nontrivial H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E H]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ H]

include hLie in
/-- The actual specified finite progression in a connected Lie model maps to a
smooth central curve with nonzero tangent. All finite progression, uniform
centrality and exact image statements are retained in the same witnesses. -/
theorem strong_local_connected_central_lie_curve (K : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ (ι : Type*) (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Fintype (G i)]
        (L : ∀ i, LocalGroupAlgebra (G i))
        (_hd : ∀ i, (L i).DivisionClosed) (_hr : ∀ i, (L i).Reversible)
        (A : ∀ i, Finset (G i)),
        (∀ i, IsStrongLocalFiniteApproximateGroup (L i) K (A i)) →
        (∀ i, (L i).IsNSS (A i : Set (G i))) →
        (∀ i, ∃ g ∈ A i, g ≠ (L i).one) →
        ∀ (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
          (V : Set H), IsCompact V →
          (∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1) →
          (∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V) →
          ∀ W : Set H, IsOpen W → (1 : H) ∈ W →
          (∀ z, π.toFun z ∈ W → z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))) →
          (∀ y ∈ W, ∃ z, π.toFun z = y) →
          ∃ (N : ι → ℕ) (P : ∀ i, Finset (G i)) (φ : ℝ → H),
            (∀ i, 2 ≤ N i ∧ (P i).card = 2*N i-1 ∧ (P i : Set (G i)) ⊆ A i ∧
              (L i).CentralLocalSet (P i : Set (G i))
                {x | (L i).escapeNorm (A i) x < 1/1001} {x | (L i).escapeNorm (A i) x < δ}) ∧
            (∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i) ∧
            Continuous φ ∧ φ 0 = 1 ∧ (∀ s t : ℝ, φ (s+t) = φ s*φ t) ∧ φ 1 ≠ 1 ∧
            (∀ t : ℝ, ∀ y : H, Commute (φ t) y) ∧
            π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))) =
              φ '' Set.Icc (-1 : ℝ) 1 ∧
            ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ φ ∧
            ∃ v : E, v ≠ 0 ∧
              HasDerivAt (fun t => (chartAt E (1 : H)) (φ t)-(chartAt E (1 : H)) 1) v 0 := by
  obtain ⟨δ,hδ,hδhalf,hcurve⟩ := strong_local_connected_central_curve K
  refine ⟨δ,hδ,hδhalf,?_⟩
  intro ι U G _ L hd hr A hA hNSS hne π V hV hVNSS himage W hWo hW1 hsmall hthick
  obtain ⟨N,P,φ,hP,hN,hcont,h0,hadd,h1,hcentral,heq⟩ :=
    hcurve ι U G L hd hr A hA hNSS hne H π V hV hVNSS himage W hWo hW1 hsmall hthick
  exact ⟨N,P,φ,hP,hN,hcont,h0,hadd,h1,hcentral,heq,
    lieGroup_one_parameter_contMDiff (E := E) φ h0 hcont.continuousAt hadd,
    lieGroup_one_parameter_nonzero_derivative (E := E) φ h0 hcont.continuousAt hadd ⟨1,h1⟩⟩
end DirectedCycles
