module

public import DirectedCycles.LocalLieTargetFirstExitAnnulus
public import DirectedCycles.LocalToLocalScaledCurve

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
variable {H E : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E H]
    {Q : LocalGroupAlgebra H} (D : LocalExponentialData (E := E) Q)

/-- The actual finite first-exit data and exponential sandwich construct a
continuous model curve with a nonzero tangent in the specified annulus. -/
theorem local_lie_target_first_exit_curve
    (hQ : LocalGroupSmoothness (E := E) Q)
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hM : ∀ᶠ i in (U : Filter ι), 2*N i ≤ M i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (hexit : ∀ᶠ i in (U : Filter ι), (p i).power (N i) ∉ A i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (V : Set H)
    (htrap : ∀ O : Set H, O ∈ 𝓝 Q.one → ∃ k : ℕ, 1 ≤ k ∧
      ∀ x : H, (∀ n ≤ k, Q.PowerIn V x n) → x ∈ O)
    (hNSS : ∀ x : H, ∀ q : Q.PowerSequence x, (∀ n, q.power n ∈ V) → x = Q.one)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 ≤ σ) (hσR : σ < D.radius)
    (houter : ∀ z ∈ localUltraSet (U : Filter ι) G A,
      π.toFun z ∈ D.chart '' Metric.closedBall (0 : E) σ)
    (hinner : ∀ z, π.toFun z ∈ D.chart '' Metric.ball (0 : E) ρ →
      z ∈ localUltraSet (U : Filter ι) G A) :
    ∃ (φ : ℝ → H) (v : E), ContinuousAt φ 0 ∧ φ 0 = Q.one ∧
      (∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (φ s) (φ t) (φ (s+t))) ∧ v ≠ 0 ∧
      HasDerivAt (fun t => D.baseChart.symm (φ t)) v 0 ∧
      (∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u N M p t)) ∧
      (ρ ≤ ‖v‖ ∧ ‖v‖ ≤ σ) ∧ ∀ t : ℝ, |t| ≤ 1 → φ t = D.chart (t • v) := by
  have hzero : Q.one ∈ D.chart '' Metric.ball (0 : E) ρ :=
    ⟨0,by simpa only [Metric.mem_ball,dist_self] using hρ,D.zero⟩
  obtain ⟨φ,hcont,h0,hadd,_,hform⟩ := exists_local_to_local_scaled_curve U G L Q hd hr A u N M p
    hN hM hi hprev hexit π V hNSS htrap himage _ hzero hinner
  have hf : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u N M p t) := fun t _ => hform t
  obtain ⟨v,hv,hbounds,heq⟩ := local_lie_target_first_exit_annulus U G L D hQ hd hr A u N M p
    hN hM hi hprev hexit π V hNSS himage φ h0 hcont hadd hf hσ hσR houter hinner
  refine ⟨φ,v,hcont,h0,hadd,?_,hv,hf,hbounds,heq⟩
  intro he
  have hh := hbounds.1
  rw [he,norm_zero] at hh
  linarith
end DirectedCycles
