import DirectedCycles.LocalLieTargetFirstExitCurve
import DirectedCycles.LocalExponentialNestedScales
import DirectedCycles.LocalToLocalInnerExitUnbounded
import DirectedCycles.LocalToLocalNestedSegmentComparison

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
theorem local_lie_target_nested_first_exit_geometry
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
    (hBo : ∀ z ∈ localUltraSet (U : Filter ι) G B,
      π.toFun z ∈ D.chart '' Metric.closedBall (0 : E) ((1001/1000)*δ*r))
    (hBs : ∀ z, π.toFun z ∈ D.chart '' Metric.ball (0 : E) (δ*r) →
      z ∈ localUltraSet (U : Filter ι) G B)
    (φ : ℝ → H)
    (hφform : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u N M p t))
    {X : E} (hφnorm : r ≤ ‖X‖ ∧ ‖X‖ ≤ (1001/1000)*r)
    (hφexp : ∀ t : ℝ, |t| ≤ 1 → φ t = D.chart (t • X)) :
    ∃ (ψ : ℝ → H) (t : ℝ), ContinuousAt ψ 0 ∧ ψ 0 = Q.one ∧
      (∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (ψ s) (ψ t) (ψ (s+t))) ∧
      (∀ s : ℝ, |s| ≤ 1 → ψ s = π.toFun (localScaledPower U G L u K J q s)) ∧
      (99/100)*δ < t ∧ t < (101/100)*δ ∧
      (∀ s : ℝ, |s| ≤ 1 → ψ s = D.chart ((t*s) • X)) ∧
      Filter.Tendsto (fun i => (K i : ℝ)/(N i : ℝ)) (U : Filter ι) (𝓝 t) ∧
      (∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < K i) ∧
      ∀ᶠ i in (U : Filter ι), (99/100)*δ < (K i : ℝ)/(N i : ℝ) ∧
        (K i : ℝ)/(N i : ℝ) < (101/100)*δ := by
  have hsub : localUltraSet (U : Filter ι) G B ⊆ localUltraSet (U : Filter ι) G A :=
    (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) B A).2 hBA
  have hsmallR : (1001/1000)*δ*r < D.radius := by
    have hh := mul_le_mul_of_nonneg_right hδ1 (show 0 ≤ (1001/1000)*r by positivity)
    nlinarith
  have hK := local_to_local_inner_first_exit_unbounded U G L Q A B u N M K J p q hN
    (hM.mono fun _ h => by omega) (hJ.mono fun _ h => by omega) hAp hBe π V hNSS himage
    (fun z hz => hBs z ⟨0,by simpa only [Metric.mem_ball,dist_self] using mul_pos hδ hr0,
      D.zero.trans hz.symm⟩)
  obtain ⟨ψ,w,hψc,hψ0,hψadd,_,_,hψform,hψnorm,hψexp⟩ :=
    local_lie_target_first_exit_curve U G L D hQ hd hr B u K J q hK hJ hBi hBp hBe π V htrap hNSS
      (fun z hz => himage z (hsub hz)) (mul_pos hδ hr0) (by positivity) hsmallR hBo hBs
  have hKN : ∀ᶠ i in (U : Filter ι), K i ≤ N i ∧ K i ≤ J i := by
    filter_upwards [hM,hJ,hBA,hBp,hAe] with i hmi hji hbai hbpi haei
    refine ⟨?_,by omega⟩
    by_contra hh
    have hn : N i < K i := lt_of_not_ge hh
    have he := ((p i).product (N i) (by omega)).unique (L i) ((q i).product (N i) (by omega))
    exact haei (he.symm ▸ hbai (hbpi _ hn))
  obtain ⟨t,ht,hlim,he⟩ := local_to_local_nested_segment_comparison U G L Q hd hr A u N M K J p q hN hM hKN hAi hAp
    π V hNSS himage φ ψ hφform (hψform 1 (by norm_num))
  have heq : D.chart w = D.chart (t • X) := by
    have hh := he
    rw [hψexp 1 (by norm_num),one_smul,hφexp t (by rw [abs_of_nonneg ht.1]; exact ht.2)] at hh
    exact hh
  obtain ⟨hw,hlo,hhi⟩ := D.signed_nested_scales hr0 hδ hδ1 hR
    (by rw [abs_of_nonneg ht.1]; exact ht.2) heq hψnorm hφnorm
  rw [abs_of_nonneg ht.1] at hlo hhi
  refine ⟨ψ,t,hψc,hψ0,hψadd,hψform,hlo,hhi,?_,hlim,hK,
    hlim.eventually (Ioo_mem_nhds hlo hhi)⟩
  intro s hs
  rw [hψexp s hs,hw,smul_smul,mul_comm s t]
end DirectedCycles
