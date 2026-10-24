import DirectedCycles.LocalLieFirstExitCurve
import DirectedCycles.LieNestedEscapeScales
import DirectedCycles.LocalInnerExitUnbounded

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
variable {H E : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E H]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ H]

include hLie in
/-- Actual nested first-exit times have ratios between .99δ and 1.01δ
eventually. All curve and tangent witnesses are constructed from the finite
segments; the scale ordering is derived from source-set inclusion. -/
theorem local_nested_escape_ratio
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
      z ∈ localUltraSet (U : Filter ι) G B) :
    ∃ t ∈ Set.Ioo ((99/100)*δ) ((101/100)*δ),
      Filter.Tendsto (fun i => (K i : ℝ)/(N i : ℝ)) (U : Filter ι) (𝓝 t) ∧
      ∀ᶠ i in (U : Filter ι), (99/100)*δ < (K i : ℝ)/(N i : ℝ) ∧
        (K i : ℝ)/(N i : ℝ) < (101/100)*δ := by
  have hsub : localUltraSet (U : Filter ι) G B ⊆ localUltraSet (U : Filter ι) G A :=
    (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) B A).2 hBA
  have hsmallR : (1001/1000)*δ*r < R := by
    have hh := mul_le_mul_of_nonneg_right hδ1 (show 0 ≤ (1001/1000)*r by positivity)
    nlinarith
  obtain ⟨φ,v,hφc,hφ0,hφadd,_,hφv,hφform,hφnorm,_⟩ :=
    local_lie_first_exit_curve U G L hd hr A u N M p hN hM hAi hAp hAe π V hV hNSS himage
      hr0 (by positivity) hR hinj hAo hAs
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
    hψc.continuousAt hφc.continuousAt hψadd hφadd hψw hφv he hψnorm hφnorm
  exact ⟨t,htight,hlim,hlim.eventually (Ioo_mem_nhds htight.1 htight.2)⟩
end DirectedCycles
