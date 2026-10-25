module

public import DirectedCycles.LocalLieTargetFirstExitCurve
public import DirectedCycles.LocalExponentialNestedScales
public import DirectedCycles.LocalToLocalInnerExitUnbounded
public import DirectedCycles.LocalToLocalNestedSegmentComparison
public import DirectedCycles.LocalLieTargetNestedFirstExitGeometry

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
variable {H E : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E H]
    {Q : LocalGroupAlgebra H} (D : LocalExponentialData (E := E) Q)

/-- The inner first-exit curve and its positive scale ratio are constructed
against the supplied outer curve, retaining the same generator and segment.
This prevents independently chosen central and inner curves from being
silently identified in the lifting argument. -/
theorem local_lie_target_nested_escape_ratio
    (hQ : LocalGroupSmoothness (E := E) Q)
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A B : ∀ i, Set (G i)) (u : ∀ i, G i) (N M K J : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (q : ∀ i, (L i).PowerSegment (u i) (J i))
    (hBA : ∀ᶠ i in (U : Filter ι), B i ⊆ A i)
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hM : ∀ᶠ i in (U : Filter ι), 2*N i ≤ M i)
    (hJ : ∀ᶠ i in (U : Filter ι), 2*K i ≤ J i)
    (hAi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hBi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ B i, (L i).inv x ∈ B i)
    (hAp : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (hBp : ∀ᶠ i in (U : Filter ι), ∀ n < K i, (q i).power n ∈ B i)
    (hAe : ∀ᶠ i in (U : Filter ι), (p i).power (N i) ∉ A i)
    (hBe : ∀ᶠ i in (U : Filter ι), (q i).power (K i) ∉ B i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (V : Set H)
    (htrap : ∀ O : Set H, O ∈ 𝓝 Q.one → ∃ k : ℕ, 1 ≤ k ∧
      ∀ x : H, (∀ n ≤ k, Q.PowerIn V x n) → x ∈ O)
    (hNSS : ∀ x : H, ∀ q : Q.PowerSequence x, (∀ n, q.power n ∈ V) → x = Q.one)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V)
    {r δ : ℝ} (hr0 : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : (1001/1000)*r < D.radius)
    (hAo : ∀ z ∈ localUltraSet (U : Filter ι) G A,
      π.toFun z ∈ D.chart '' Metric.closedBall (0 : E) ((1001/1000)*r))
    (hAs : ∀ z, π.toFun z ∈ D.chart '' Metric.ball (0 : E) r →
      z ∈ localUltraSet (U : Filter ι) G A)
    (hBo : ∀ z ∈ localUltraSet (U : Filter ι) G B,
      π.toFun z ∈ D.chart '' Metric.closedBall (0 : E) ((1001/1000)*δ*r))
    (hBs : ∀ z, π.toFun z ∈ D.chart '' Metric.ball (0 : E) (δ*r) →
      z ∈ localUltraSet (U : Filter ι) G B)
:
    ∃ t ∈ Set.Ioo ((99/100)*δ) ((101/100)*δ),
      Filter.Tendsto (fun i => (K i : ℝ)/(N i : ℝ)) (U : Filter ι) (𝓝 t) ∧
      ∀ᶠ i in (U : Filter ι), (99/100)*δ < (K i : ℝ)/(N i : ℝ) ∧
        (K i : ℝ)/(N i : ℝ) < (101/100)*δ := by
  obtain ⟨φ,v,_,_,_,_,_,hφform,hφnorm,hφexp⟩ :=
    local_lie_target_first_exit_curve U G L D hQ hd hr A u N M p hN hM hAi hAp hAe
      π V htrap hNSS himage hr0 (by positivity) hR hAo hAs
  obtain ⟨_,t,_,_,_,_,hlo,hhi,_,hlim,_,hbound⟩ :=
    local_lie_target_nested_first_exit_geometry U G L D hQ hd hr A B u N M K J p q
      hBA hN hM hJ hAi hBi hAp hBp hAe hBe π V htrap hNSS himage
      hr0 hδ hδ1 hR hBo hBs φ hφform hφnorm hφexp
  exact ⟨t,⟨hlo,hhi⟩,hlim,hbound⟩
end DirectedCycles
