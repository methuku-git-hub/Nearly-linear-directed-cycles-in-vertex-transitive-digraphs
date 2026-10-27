module

public import DirectedCycles.LocalFirstExitTangent
public import DirectedCycles.LocalScaledModel
public import DirectedCycles.LieOneParameterNonzero

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
variable {H E : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E H]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ H]

include hLie in
/-- The actual finite first-exit data and exponential sandwich construct a
continuous model curve with a nonzero tangent in the specified annulus. -/
theorem local_lie_first_exit_curve
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hM : ∀ᶠ i in (U : Filter ι), 2*N i ≤ M i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (hexit : ∀ᶠ i in (U : Filter ι), (p i).power (N i) ∉ A i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hV : IsCompact V)
    (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V)
    {R ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 ≤ σ) (hσR : σ < R)
    (hinj : Set.InjOn (lieExponential (G := H) (E := E)) (Metric.ball 0 R))
    (houter : ∀ z ∈ localUltraSet (U : Filter ι) G A,
      π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) σ)
    (hinner : ∀ z, π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) ρ →
      z ∈ localUltraSet (U : Filter ι) G A) :
    ∃ (φ : ℝ → H) (v : E), Continuous φ ∧ φ 0 = 1 ∧
      (∀ s t : ℝ, φ (s+t) = φ s*φ t) ∧ v ≠ 0 ∧
      HasDerivAt (fun t => chartAt E (1 : H) (φ t)-chartAt E (1 : H) 1) v 0 ∧
      (∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u N M p t)) ∧
      (ρ ≤ ‖v‖ ∧ ‖v‖ ≤ σ) ∧ ∀ t : ℝ, φ t = lieExponential (G := H) (t • v) := by
  have hzero : (1 : H) ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) ρ :=
    ⟨0,by simpa only [Metric.mem_ball,dist_self] using hρ,lieExponential_zero⟩
  obtain ⟨φ,hcont,h0,hadd,h1,hform⟩ := exists_local_scaled_one_parameter U G L hd hr A u N M p
    hN hM hi hprev hexit π V hV hNSS himage _ hzero hinner
  obtain ⟨v,hv,hD⟩ := lieGroup_one_parameter_nonzero_derivative (E := E) φ h0 hcont.continuousAt hadd ⟨1,h1⟩
  exact ⟨φ,v,hcont,h0,hadd,hv,hD,hform,
    local_first_exit_tangent_annulus U G L hd hr A u N M p hN hM hi hprev hexit π V hNSS himage
      φ h0 hcont.continuousAt hadd hform hD hσ hσR hinj houter hinner,
    lie_one_parameter_eq_exponential φ h0 hcont.continuousAt hadd hD⟩
end DirectedCycles
