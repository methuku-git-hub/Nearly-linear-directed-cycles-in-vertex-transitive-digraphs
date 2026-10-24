import DirectedCycles.StrongLocalLieTargetCentralReductionData
import DirectedCycles.LocalToLocalCentralGeneratorEscape
import DirectedCycles.LocalCentralQuotientCompactNSS
import DirectedCycles.LocalLieTargetPrescribedEscapeQuotient
import DirectedCycles.LocalToLocalCentralComponentNeighbourhood
import DirectedCycles.LocalExponentialBallTopology

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles
variable {ι H E : Type*} [TopologicalSpace H] [T2Space H] [LocallyCompactSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    [ChartedSpace E H] [IsManifold 𝓘(ℝ,E) ∞ H]
    {Q : LocalGroupAlgebra H} (Y : LocalExponentialData (E := E) Q)

/-- Central reduction from an actual smooth local Lie model. The finite
central progression, lower-dimensional smooth local target, finite quotient
windows, their good-model neighbourhoods, density and escape-controlled lifts
are constructed together. In particular finite quotient NSS is a conclusion.
The target retains all local smoothness and algebraic properties required for another reduction. -/
theorem local_lie_target_central_reduction
    (hQ : LocalGroupSmoothness (E := E) Q) (hdQ : Q.DivisionClosed) (hrQ : Q.Reversible)
    (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Fintype (G i)]
    (L : ∀ i, LocalGroupAlgebra (G i)) (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Finset (G i)) {Ka : ℕ} (hA : ∀ i, IsStrongLocalFiniteApproximateGroup (L i) Ka (A i))
    (hANSS : ∀ i, (L i).IsNSS (A i : Set (G i)))
    (hne : ∀ i, ∃ g ∈ A i, g ≠ (L i).one)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    {ra : ℝ} (hra : 0 < ra) (hRa : 10*ra < Y.radius)
    (hAo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
      π.toFun z ∈ Y.chart '' Metric.closedBall (0 : E) ((1001/1000)*ra))
    (hAs : ∀ z, π.toFun z ∈ Y.chart '' Metric.ball (0 : E) ra →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (V : Set H) (hV : IsCompact V) (hVNSS : ∀ x : H, ∀ q : Q.PowerSequence x, (∀ n, q.power n ∈ V) → x = Q.one)
    (htrap : ∀ O : Set H, O ∈ 𝓝 Q.one → ∃ n : ℕ, 1 ≤ n ∧
      ∀ x : H, (∀ j ≤ n, Q.PowerIn V x j) → x ∈ O)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V)
    (U₀ : Set H) (hU₀ : IsOpen U₀) (hU₀1 : Q.one ∈ U₀)
    (hsmall : π.toFun ⁻¹' U₀ ⊆ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hthick : ∀ y ∈ U₀, ∃ z, π.toFun z = y)
    (hsandwich : ∀ F O : Set H, IsCompact F → IsOpen O → F ⊆ O → O ⊆ U₀ →
      ∃ B : ∀ i, Finset (G i),
        π.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆ π.toFun ⁻¹' O) :
    ∃ (τ : ℝ), 0 < τ ∧ τ ≤ 1/2 ∧
    ∃ (u : ∀ i, G i) (N : ι → ℕ) (p : ∀ i, (L i).PowerSegment (u i) (2*N i))
      (P : ∀ i, Finset (G i)) (φ : ℝ → H),
      (∀ i, 2 ≤ N i ∧ u i ∈ A i ∧ u i ≠ (L i).one ∧
        (∀ n < N i, (p i).power n ∈ A i) ∧ (p i).power (N i) ∉ A i ∧
        (L i).escapeNorm (A i) (u i) = 1/(N i : ℝ) ∧ (P i : Set (G i)) = (p i).shortSignedSet (N i) ∧
        (P i).card = 2*N i-1 ∧ (P i : Set (G i)) ⊆ A i ∧
        (L i).CentralLocalSet (P i : Set (G i))
          {x | (L i).escapeNorm (A i) x < 1/1001} {x | (L i).escapeNorm (A i) x < τ}) ∧
      (∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i) ∧
      ContinuousAt φ 0 ∧ φ 0 = Q.one ∧
      (∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (φ s) (φ t) (φ (s+t))) ∧ φ 1 ≠ Q.one ∧
      π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))) = φ '' Set.Icc (-1 : ℝ) 1 ∧
      ∃ (v : E) (ℓ : E →L[ℝ] ℝ), v ≠ 0 ∧ ℓ v = 1 ∧
        Module.finrank ℝ ℓ.ker + 1 = Module.finrank ℝ E ∧
      ∃ T : Q.CentralQuotientData (φ '' Set.Icc (-1 : ℝ) 1),
        IsOpen T.small ∧ T.algebra.DivisionClosed ∧ T.algebra.Reversible ∧
        T2Space T.Carrier ∧ LocallyCompactSpace T.Carrier ∧
        ∃ cs : ChartedSpace ℓ.ker T.Carrier,
          let := cs
          IsManifold 𝓘(ℝ,ℓ.ker) ∞ T.Carrier ∧
          LocalGroupSmoothness (E := ℓ.ker) T.algebra ∧
          ∃ K J : ℕ, 1 ≤ K ∧ 1 ≤ J ∧
          ∃ B : ∀ i, Finset (G i), ∃ D : ∀ i, (L i).CentralQuotientData (P i : Set (G i)),
          (∀ i, IsLocalFiniteApproximateGroup (L i) K (B i) ∧ B i ⊆ A i ∧
            (D i).small = (L i).wordPower (B i : Set (G i)) 200 ∧
            (∀ n ≤ 200, (L i).wordPower (B i : Set (G i)) n ⊆ (D i).small) ∧
            (D i).small ⊆ {x | (L i).escapeNorm (A i) x < τ} ∧
            IsLocalFiniteApproximateGroup (D i).algebra K ((D i).finiteImage (B i)) ∧
            (D i).algebra.DivisionClosed ∧ (D i).algebra.Reversible) ∧
          (∀ᶠ i in (U : Filter ι), IsStrongLocalFiniteApproximateGroup (L i) K (B i)) ∧
          (∀ᶠ i in (U : Filter ι), (A i).card ≤ J*((D i).finiteImage (B i)).card*(P i).card) ∧
          (∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ i in (U : Filter ι),
            (L i).escapeNorm (B i) (u i) ≤ C₀/((N i : ℝ)+1)) ∧
          ∃ Ψ : LocalGroupHom
            (localUltraAlgebra (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).algebra))
            T.algebra,
          ∃ Vq O : Set T.Carrier,
            IsCompact Vq ∧ (∀ z, Ψ.toFun z ∈ Vq) ∧
            (∀ x, ∀ q : T.algebra.PowerSequence x,
              (∀ n, q.power n ∈ Vq) → x = T.algebra.one) ∧
            (∀ W : Set T.Carrier, W ∈ 𝓝 T.algebra.one → ∃ n : ℕ, 1 ≤ n ∧
              ∀ x, (∀ j ≤ n, T.algebra.PowerIn Vq x j) → x ∈ W) ∧
            IsOpen O ∧ T.algebra.one ∈ O ∧
            Ψ.toFun ⁻¹' O ⊆ localUltraSet (U : Filter ι) (fun i => (D i).Carrier)
              (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier)) ∧
            O ⊆ Ψ.toFun '' localUltraSet (U : Filter ι) (fun i => (D i).Carrier)
              (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier)) ∧
            (∀ F O' : Set T.Carrier, IsCompact F → IsOpen O' → F ⊆ O' →
              ∃ S : ∀ i, Finset (D i).Carrier,
                Ψ.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) (fun i => (D i).Carrier) (fun i => (S i : Set (D i).Carrier)) ∧
                localUltraSet (U : Filter ι) (fun i => (D i).Carrier) (fun i => (S i : Set (D i).Carrier)) ⊆ Ψ.toFun ⁻¹' O') ∧
            ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in (U : Filter ι),
              (∀ y ∈ (D i).finiteImage (B i), ∃ x : (D i).small, x.val ∈ B i ∧ (D i).project x = y ∧
                (L i).escapeNorm (B i : Set (G i)) x.val ≤
                  C*(D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier) y) ∧
              (D i).algebra.IsNSS ((D i).finiteImage (B i) : Set (D i).Carrier) := by
  obtain ⟨τ,hτ,hτhalf,hcentral⟩ := strong_local_lie_target_central_reduction_data Ka
  obtain ⟨u,N,p,P,φ,hP,hPexact,huData,hφform,hPimage,hNu,hφc,hφ0,hφadd,hφ1,_,_,_,
    v,ℓ,hv,hℓ,hdim,T,hWo,hTdiv,hTrev,hT2,hTlc,a,_,_,hWa,hrel,cs,hman,hsmooth⟩ :=
    hcentral ι U G L hd hr A hA hANSS hne H E Q hQ hdQ hrQ π V hVNSS htrap himage
      U₀ hU₀ hU₀1 hsmall hthick
  choose hN2 hPcard hPA hPlocal using hP
  choose hu hu1 hup hue hnorm hmin hcent _hp4 using huData
  let := hT2
  let := hTlc
  let := cs
  let := hman
  obtain ⟨Vq,_hVqn,hVqc,hqNSS,hqtrap,Z,hZ,hZ1,hZW,hZU₀,hZVq⟩ :=
    T.exists_compact_nss_source_window hWo hsmooth U₀ (hU₀.mem_nhds hU₀1)
  obtain ⟨K,R,hK,hR,hwin⟩ := local_lie_target_prescribed_escape_controlled_central_model Y hQ U G L hd hr A
    (fun i => (hA i).approximate) hANSS u N p hN2 hup hue hu1 hnorm hmin hNu π hra hRa hAo hAs
    φ hφ0 hφc hφadd (fun t _ => hφform t) V hV hVNSS htrap himage U₀ hU₀ hU₀1 hsmall hsandwich
    P hτ hPlocal hPexact hcent T hWo hPimage Vq hqNSS Z hZ hZ1 hZW hZU₀ hZVq
  obtain ⟨Rs,hRs,hsand⟩ := Y.ball_sandwich U₀ (hU₀.mem_nhds hU₀1)
  let r := min R (min Y.radius Rs)/2
  have hr0 : 0 < r := div_pos (lt_min hR (lt_min Y.radius_pos hRs)) (by norm_num)
  have hrR : r < R := by dsimp only [r]; linarith [min_le_left R (min Y.radius Rs)]
  have hrRo : r ≤ Y.radius := by dsimp only [r]; linarith [min_le_right R (min Y.radius Rs),min_le_left Y.radius Rs]
  have hrRs : r < Rs := by dsimp only [r]; linarith [min_le_right R (min Y.radius Rs),min_le_right Y.radius Rs]
  obtain ⟨B,D,J,hJ,hBin,hBout,hB,hstrong,hcard,Ψ,⟨hDW,hΨ⟩,_hkernel,himageq,hsw,hbound⟩ := hwin r hr0 hrR
  have hcentralBound := local_to_local_central_generator_escape_bound Q U G L hd hr
    (fun i => (A i : Set (G i))) (fun i => (B i : Set (G i)))
    (fun i => (hB i).1.one_mem) (fun i => (hB i).2.1) (fun i => (hA i).approximate.inv_mem)
    u N p (fun i => by have := hN2 i; omega) hNu hup hue π V hVNSS himage (by
      intro z hz
      apply hBin
      exact ⟨0,by simpa only [Metric.mem_closedBall,dist_self] using hr0.le,Y.zero.trans hz.symm⟩)
  let S : Set H := Y.chart '' Metric.ball (0 : E) r
  have hSo : IsOpen S := Y.ball_open hrRo
  have hS1 : Q.one ∈ S := ⟨0,by simpa only [Metric.mem_ball,dist_self] using hr0,Y.zero⟩
  have hSU₀ : S ⊆ U₀ := by
    apply Set.Subset.trans _ (hsand r hr0 hrRs).2.2.2.1
    exact Set.image_mono (Metric.ball_subset_ball (by linarith))
  have hPQ : ∀ x ∈ localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))),
      π.toFun x ∈ φ '' Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    rw [← hPimage]
    exact ⟨x,hx,rfl⟩
  have hBsmall : ∀ i, (B i : Set (G i)) ⊆ (D i).small := by
    intro i
    rw [← (L i).wordPower_one (B i : Set (G i))]
    exact (hB i).2.2.2.1 1 (by omega)
  have hDsmall : ∀ i, (D i).small ⊆ A i := by
    intro i x hx
    have he : (L i).escapeNorm (A i) x < τ := (hB i).2.2.2.2.1 hx
    exact (L i).mem_of_escapeNorm_lt_one (hA i).approximate.one_mem (by linarith)
  let O := T.project '' {x : T.small | x.val ∈ S}
  have hOo : IsOpen O := T.isOpenMap_project a hWo hWa hrel _ (hSo.preimage continuous_subtype_val)
  have hO1 : T.algebra.one ∈ O := ⟨⟨Q.one,T.one_mem⟩,hS1,rfl⟩
  have hneigh := LocalGroupAlgebra.CentralQuotientData.localComponentModel_neighbourhood U G L
    (fun i => (P i : Set (G i))) D hd hr T hdQ π hPQ hDW
    (by rw [hPimage]) (fun i => (hPlocal i).inv_mem) A B hPA hDsmall
    (fun i => (hA i).approximate.inv_mem)
    (fun i => (hA i).approximate.allProducts.mono (L i) (Set.Subset.refl _) (by omega : 2 ≤ 200)) hBsmall S
    (fun _ hx => hBin (Set.image_mono Metric.ball_subset_closedBall hx)) (fun y hy => hthick y (hSU₀ hy))
  rw [← hΨ hPQ] at hneigh
  exact ⟨τ,hτ,hτhalf,u,N,p,P,φ,fun i => ⟨hN2 i,hu i,hu1 i,hup i,hue i,hnorm i,hPexact i,hPcard i,hPA i,hPlocal i⟩,
    hNu,hφc,hφ0,hφadd,hφ1,hPimage,v,ℓ,hv,hℓ,hdim,T,hWo,hTdiv,hTrev,hT2,hTlc,cs,hman,
    hsmooth,K,J,hK,hJ,B,D,hB,hstrong,hcard,hcentralBound,Ψ,Vq,O,hVqc,himageq,hqNSS,hqtrap,hOo,hO1,hneigh.1,hneigh.2,hsw,hbound⟩
end DirectedCycles
