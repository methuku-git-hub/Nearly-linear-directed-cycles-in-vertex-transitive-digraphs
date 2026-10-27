module

public import DirectedCycles.LocalLieFirstExitCurve
public import DirectedCycles.LieNestedEscapeScales
public import DirectedCycles.LocalInnerExitUnbounded
public import DirectedCycles.LieCurveCoordinateComparison

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
variable {H E : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E H]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ H]

include hLie in
/-- The inner first-exit curve and its positive scale ratio are constructed
against the supplied outer curve, retaining the same generator and segment.
This prevents independently chosen central and inner curves from being
silently identified in the lifting argument. -/
theorem local_nested_first_exit_geometry
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
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hV : IsCompact V)
    (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V)
    {R r δ : ℝ} (hr0 : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : (1001/1000)*r < R)
    (hinj : Set.InjOn (lieExponential (G := H) (E := E)) (Metric.ball 0 R))
    (hAo : ∀ z ∈ localUltraSet (U : Filter ι) G A,
      π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000)*r))
    (hAs : ∀ z, π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) r →
      z ∈ localUltraSet (U : Filter ι) G A)
    (hBo : ∀ z ∈ localUltraSet (U : Filter ι) G B,
      π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000)*δ*r))
    (hBs : ∀ z, π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) (δ*r) →
      z ∈ localUltraSet (U : Filter ι) G B)
    (φ : ℝ → H) (hφ0 : φ 0 = 1) (hφc : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t)
    (hφform : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u N M p t))
    {X : E} (hφX : HasDerivAt (fun t => chartAt E (1 : H) (φ t)-chartAt E (1 : H) 1) X 0) :
    ∃ (ψ : ℝ → H) (t : ℝ), Continuous ψ ∧ ψ 0 = 1 ∧
      (∀ s t : ℝ, ψ (s+t) = ψ s*ψ t) ∧
      (∀ s : ℝ, |s| ≤ 1 → ψ s = π.toFun (localScaledPower U G L u K J q s)) ∧
      (99/100)*δ < t ∧ t < (101/100)*δ ∧
      (∀ s : ℝ, ψ s = lieExponential (G := H) ((t*s) • X)) ∧
      Filter.Tendsto (fun i => (K i : ℝ)/(N i : ℝ)) (U : Filter ι) (𝓝 t) ∧
      (∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < K i) ∧
      ∀ᶠ i in (U : Filter ι), (99/100)*δ < (K i : ℝ)/(N i : ℝ) ∧
        (K i : ℝ)/(N i : ℝ) < (101/100)*δ := by
  have hsub : localUltraSet (U : Filter ι) G B ⊆ localUltraSet (U : Filter ι) G A :=
    (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) B A).2 hBA
  have hsmallR : (1001/1000)*δ*r < R := by
    have hh := mul_le_mul_of_nonneg_right hδ1 (show 0 ≤ (1001/1000)*r by positivity)
    nlinarith
  have hφnorm := local_first_exit_tangent_annulus U G L hd hr A u N M p hN hM hAi hAp hAe
    π V hNSS himage φ hφ0 hφc hφadd hφform hφX (by positivity) hR hinj hAo hAs
  have hK := local_inner_first_exit_unbounded U G L A B u N M K J p q hN
    (hM.mono fun _ h => by omega) (hJ.mono fun _ h => by omega) hAp hBe π V hNSS himage
    (fun z hz => hBs z ⟨0,by simpa only [Metric.mem_ball,dist_self] using mul_pos hδ hr0,
      lieExponential_zero.trans hz.symm⟩)
  obtain ⟨ψ,w,hψc,hψ0,hψadd,_,hψw,hψform,hψnorm,_⟩ :=
    local_lie_first_exit_curve U G L hd hr B u K J q hK hJ hBi hBp hBe π V hV hNSS
      (fun z hz => himage z (hsub hz)) (mul_pos hδ hr0) (by positivity) hsmallR hinj hBo hBs
  have hKN : ∀ᶠ i in (U : Filter ι), K i ≤ N i ∧ K i ≤ J i := by
    filter_upwards [hM,hJ,hBA,hBp,hAe] with i hmi hji hbai hbpi haei
    refine ⟨?_,by omega⟩
    by_contra hh
    have hn : N i < K i := lt_of_not_ge hh
    have he := ((p i).product (N i) (by omega)).unique (L i) ((q i).product (N i) (by omega))
    exact haei (he.symm ▸ hbai (hbpi _ hn))
  obtain ⟨t,ht,hlim,he⟩ := local_nested_segment_comparison U G L hd hr A u N M K J p q hN hM hKN hAi hAp
    π V hNSS himage φ ψ hφform (hψform 1 (by norm_num))
  have htight := lie_nested_escape_scales hr0 hδ hδ1 hR ht hinj ψ φ hψ0 hφ0
    hψc.continuousAt hφc hψadd hφadd hψw hφX he hψnorm hφnorm
  have hwR : ‖w‖ < R := lt_of_le_of_lt hψnorm.2 hsmallR
  have htX : |t| * ‖X‖ < R := by
    rw [abs_of_nonneg ht.1]
    have hh := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg X)
    nlinarith [hφnorm.2]
  have hagree := (lie_curve_coordinate_comparison hinj ψ φ hψ0 hφ0 hψc.continuousAt hφc
    hψadd hφadd hψw hφX he hwR htX).2
  have hexp := lie_one_parameter_eq_exponential φ hφ0 hφc hφadd hφX
  exact ⟨ψ,t,hψc,hψ0,hψadd,hψform,htight.1,htight.2,
    fun s => (hagree s).trans (hexp (t*s)),hlim,hK,
    hlim.eventually (Ioo_mem_nhds htight.1 htight.2)⟩
end DirectedCycles
