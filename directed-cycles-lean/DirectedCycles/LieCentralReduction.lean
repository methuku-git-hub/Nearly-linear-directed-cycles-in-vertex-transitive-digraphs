import DirectedCycles.StrongLocalCentralData
import DirectedCycles.LocalCentralGeneratorEscape
import DirectedCycles.LieCentralCompactNSSQuotient
import DirectedCycles.LiePrescribedEscapeQuotient
import DirectedCycles.LocalCentralComponentNeighbourhood
import DirectedCycles.LieExponentialBallTopology

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles
variable {ι H E : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [PreconnectedSpace H] [Nontrivial H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] [LieGroup 𝓘(ℝ,E) ∞ H]

/-- Central reduction from a genuine connected global Lie model. The finite
central progression, lower-dimensional smooth local target, finite quotient
windows, their good-model neighbourhoods, density and escape-controlled lifts
are constructed together. In particular finite quotient NSS is a conclusion.
Existence or globalization of the original Lie model is not asserted here. -/
theorem lie_central_reduction
    (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Fintype (G i)]
    (L : ∀ i, LocalGroupAlgebra (G i)) (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Finset (G i)) {Ka : ℕ} (hA : ∀ i, IsStrongLocalFiniteApproximateGroup (L i) Ka (A i))
    (hANSS : ∀ i, (L i).IsNSS (A i : Set (G i)))
    (hne : ∀ i, ∃ g ∈ A i, g ≠ (L i).one)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    {Ra ra : ℝ} (hra : 0 < ra) (hRa : (1001/1000)*ra < Ra)
    (hinj : Set.InjOn (lieExponential (G := H) (E := E)) (Metric.ball 0 Ra))
    (hAo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
      π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000)*ra))
    (hAs : ∀ z, π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) ra →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (V : Set H) (hV : IsCompact V) (hVNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V)
    (U₀ : Set H) (hU₀ : IsOpen U₀) (hU₀1 : (1 : H) ∈ U₀)
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
      Continuous φ ∧ φ 0 = 1 ∧ (∀ s t : ℝ, φ (s+t) = φ s*φ t) ∧ φ 1 ≠ 1 ∧
      (∀ t : ℝ, ∀ y : H, Commute (φ t) y) ∧
      π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))) = φ '' Set.Icc (-1 : ℝ) 1 ∧
      ∃ (v : E) (ℓ : E →L[ℝ] ℝ), v ≠ 0 ∧ ℓ v = 1 ∧
        Module.finrank ℝ ℓ.ker + 1 = Module.finrank ℝ E ∧
      ∃ T W : Set H, ∃ hQ : LocalNormalSet (φ '' Set.Icc (-1 : ℝ) 1) T,
        ∃ hW1 : (1 : H) ∈ W, ∃ hWi : W⁻¹ = W, ∃ hW6 : W^6 ⊆ T,
        IsOpen W ∧ T2Space (hQ.WindowQuotient hW1 hWi hW6) ∧
        ∃ cs : ChartedSpace ℓ.ker (hQ.WindowQuotient hW1 hWi hW6),
          let := cs
          IsManifold 𝓘(ℝ,ℓ.ker) ∞ (hQ.WindowQuotient hW1 hWi hW6) ∧
          LocalGroupSmoothness (E := ℓ.ker) (hQ.quotientAlgebra hW1 hWi hW6) ∧
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
            (hQ.quotientAlgebra hW1 hWi hW6),
          ∃ Vq O : Set (hQ.WindowQuotient hW1 hWi hW6),
            IsCompact Vq ∧ (∀ z, Ψ.toFun z ∈ Vq) ∧
            (∀ x, ∀ q : (hQ.quotientAlgebra hW1 hWi hW6).PowerSequence x,
              (∀ n, q.power n ∈ Vq) → x = (hQ.quotientAlgebra hW1 hWi hW6).one) ∧
            IsOpen O ∧ (hQ.quotientAlgebra hW1 hWi hW6).one ∈ O ∧
            Ψ.toFun ⁻¹' O ⊆ localUltraSet (U : Filter ι) (fun i => (D i).Carrier)
              (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier)) ∧
            O ⊆ Ψ.toFun '' localUltraSet (U : Filter ι) (fun i => (D i).Carrier)
              (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier)) ∧
            (∀ F O' : Set (hQ.WindowQuotient hW1 hWi hW6), IsCompact F → IsOpen O' → F ⊆ O' →
              ∃ S : ∀ i, Finset (D i).Carrier,
                Ψ.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) (fun i => (D i).Carrier) (fun i => (S i : Set (D i).Carrier)) ∧
                localUltraSet (U : Filter ι) (fun i => (D i).Carrier) (fun i => (S i : Set (D i).Carrier)) ⊆ Ψ.toFun ⁻¹' O') ∧
            ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in (U : Filter ι),
              (∀ y ∈ (D i).finiteImage (B i), ∃ x : (D i).small, x.val ∈ B i ∧ (D i).project x = y ∧
                (L i).escapeNorm (B i : Set (G i)) x.val ≤
                  C*(D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier) y) ∧
              (D i).algebra.IsNSS ((D i).finiteImage (B i) : Set (D i).Carrier) := by
  obtain ⟨τ,hτ,hτhalf,hcentral⟩ := strong_local_connected_central_data Ka
  obtain ⟨u,N,p,P,φ,hdata,hNu,hφc,hφ0,hφadd,hφ1,hφcent,hPimage,hφform⟩ :=
    hcentral ι U G L hd hr A hA hANSS hne H π V hV hVNSS himage U₀ hU₀ hU₀1 hsmall hthick
  choose hu hu1 hN2 hup hue hnorm hmin hcent hp4 hPexact hPcard hPA hPlocal using hdata
  have hφbound : ∀ t : ℝ, |t| ≤ 1 → φ t ∈ V := by
    intro t ht
    have hm : φ t ∈ π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))) := by
      rw [hPimage]
      exact ⟨t,abs_le.mp ht,rfl⟩
    obtain ⟨x,hx,he⟩ := hm
    rw [← he]
    exact himage x ((localUltraSet_subset_iff_eventually U G (fun i => (L i).one) _ _).2
      (Filter.Eventually.of_forall hPA) hx)
  obtain ⟨v,ℓ,hv,hℓ,hdim,T,W,hQ,hW1,hWi,hW6,hWo,hT2,cs,hman,hsmooth,Vq,hVqn,hVqc,hqNSS,
    Z,hZ,hZ1,hZW,hZU₀,hZVq⟩ := exists_lie_central_compact_nss_quotient (E := E)
    φ hφc hφ0 hφadd hφ1 hφcent V hVNSS hφbound U₀ (hU₀.mem_nhds hU₀1)
  let := hT2
  let := cs
  obtain ⟨K,R,hK,hR,hwin⟩ := lie_prescribed_escape_controlled_central_model U G L hd hr A
    (fun i => (hA i).approximate) hANSS u N p hN2 hup hue hu1 hnorm hmin hNu π hra hRa hinj hAo hAs
    φ hφ0 hφc.continuousAt hφadd hφform V hV hVNSS himage U₀ hU₀ hU₀1 hsmall hsandwich
    P hτ hPlocal hPexact hcent hQ hW1 hWi hW6 hWo hPimage Vq hqNSS Z hZ hZ1 hZW hZU₀ hZVq
  obtain ⟨Ro,hRo,hopen⟩ := lie_exponential_small_ball_open (G := H) (E := E)
  obtain ⟨Rs,hRs,hsand⟩ := lie_exponential_ball_sandwich (G := H) (E := E) U₀ (hU₀.mem_nhds hU₀1)
  let r := min R (min Ro Rs)/2
  have hr0 : 0 < r := div_pos (lt_min hR (lt_min hRo hRs)) (by norm_num)
  have hrR : r < R := by dsimp only [r]; linarith [min_le_left R (min Ro Rs)]
  have hrRo : r ≤ Ro := by dsimp only [r]; linarith [min_le_right R (min Ro Rs),min_le_left Ro Rs]
  have hrRs : r < Rs := by dsimp only [r]; linarith [min_le_right R (min Ro Rs),min_le_right Ro Rs]
  obtain ⟨B,D,J,hJ,hBin,hBout,hB,hstrong,hcard,Ψ,⟨hDW,hΨ⟩,_hkernel,himageq,hsw,hbound⟩ := hwin r hr0 hrR
  have hcentralBound := local_central_generator_escape_bound U G L hd hr
    (fun i => (A i : Set (G i))) (fun i => (B i : Set (G i)))
    (fun i => (hB i).1.one_mem) (fun i => (hB i).2.1) (fun i => (hA i).approximate.inv_mem)
    u N p (fun i => by have := hN2 i; omega) hNu hup hue π V hVNSS himage (by
      intro z hz
      apply hBin
      exact ⟨0,by simpa only [Metric.mem_closedBall,dist_self] using hr0.le,lieExponential_zero.trans hz.symm⟩)
  let S : Set H := (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) r
  have hSo : IsOpen S := hopen r hrRo
  have hS1 : (1 : H) ∈ S := ⟨0,by simpa only [Metric.mem_ball,dist_self] using hr0,lieExponential_zero⟩
  have hSU₀ : S ⊆ U₀ := by
    apply Set.Subset.trans _ (hsand r hr0 hrRs).2.2.2
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
  let O := hQ.windowMk hW1 hWi hW6 '' {x : W | x.val ∈ S}
  have hOo : IsOpen O := hQ.isOpenMap_windowMk hW1 hWi hW6 hWo _ (hSo.preimage continuous_subtype_val)
  have hO1 : (hQ.quotientAlgebra hW1 hWi hW6).one ∈ O := ⟨⟨1,hW1⟩,hS1,rfl⟩
  have hneigh := LocalGroupAlgebra.CentralQuotientData.componentModel_neighbourhood U G L
    (fun i => (P i : Set (G i))) D hd hr hQ hW1 hWi hW6 π hPQ hDW
    (by rw [hPimage]) (fun i => (hPlocal i).inv_mem) A B hPA hDsmall
    (fun i => (hA i).approximate.inv_mem)
    (fun i => (hA i).approximate.allProducts.mono (L i) (Set.Subset.refl _) (by omega : 2 ≤ 200)) hBsmall S
    (fun _ hx => hBin (Set.image_mono Metric.ball_subset_closedBall hx)) (fun y hy => hthick y (hSU₀ hy))
  rw [← hΨ hPQ] at hneigh
  exact ⟨τ,hτ,hτhalf,u,N,p,P,φ,fun i => ⟨hN2 i,hu i,hu1 i,hup i,hue i,hnorm i,hPexact i,hPcard i,hPA i,hPlocal i⟩,
    hNu,hφc,hφ0,hφadd,hφ1,hφcent,hPimage,v,ℓ,hv,hℓ,hdim,T,W,hQ,hW1,hWi,hW6,hWo,hT2,cs,hman,
    hsmooth,K,J,hK,hJ,B,D,hB,hstrong,hcard,hcentralBound,Ψ,Vq,O,hVqc,himageq,hqNSS,hOo,hO1,hneigh.1,hneigh.2,hsw,hbound⟩
end DirectedCycles
