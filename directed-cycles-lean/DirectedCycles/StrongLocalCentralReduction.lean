import DirectedCycles.StrongLocalCentralCurve
import DirectedCycles.LocalCentralQuotientModelAssembly
import DirectedCycles.CentralCurveTopologicalQuotient

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles

/-- The central reduction in an actual local ambient group: a specified
proper progression, uniformly dense finite quotients, an exact nontrivial
central model curve, a Hausdorff locally compact target quotient, and a genuine
descended local homomorphism. Lie structure, dimension decrease and quotient
NSS are not conclusions of this intermediate theorem. -/
theorem strong_local_central_reduction {ι : Type*} (U : Ultrafilter ι)
    (G : ι → Type*) [∀ i, Fintype (G i)] (L : ∀ i, LocalGroupAlgebra (G i))
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Finset (G i)) {K : ℕ} (hK : 1 ≤ K)
    (hA : ∀ i, IsStrongLocalFiniteApproximateGroup (L i) K (A i))
    (hNSS : ∀ i, (L i).IsNSS (A i : Set (G i))) (hne : ∀ i, ∃ g ∈ A i, g ≠ (L i).one)
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [PreconnectedSpace H] [Nontrivial H] [LocallyCompactSpace H]
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hV : IsCompact V) (hVNSS : ∀ y : H, (∀ n : ℕ, y^n ∈ V) → y = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V)
    (W : Set H) (hWo : IsOpen W) (hW1 : (1 : H) ∈ W)
    (hsmall : ∀ z, π.toFun z ∈ W → z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hthick : ∀ y ∈ W, ∃ z, π.toFun z = y) :
    ∃ (J : ℕ) (η : ℝ) (N : ι → ℕ) (P : ∀ i, Finset (G i)),
      1 ≤ J ∧ 0 < η ∧
      (∀ i, 2 ≤ N i ∧ (P i).card = 2*N i-1 ∧ (P i : Set (G i)) ⊆ A i) ∧
      (∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i) ∧
      ∃ D : ∀ i, (L i).CentralQuotientData (P i : Set (G i)), ∃ B : ∀ i, Finset (G i),
        (∀ i, IsLocalFiniteApproximateGroup (L i) J (B i) ∧ η*(A i).card ≤ (B i).card ∧
          (∀ n ≤ 200, (L i).wordPower (B i : Set (G i)) n ⊆ (D i).small) ∧
          IsLocalFiniteApproximateGroup (D i).algebra J ((D i).finiteImage (B i)) ∧
          η*(A i).card ≤ ((D i).finiteImage (B i)).card * ((P i).card : ℝ)) ∧
        ∃ φ : ℝ → H, Continuous φ ∧ φ 0 = 1 ∧ (∀ s t, φ (s+t) = φ s*φ t) ∧ φ 1 ≠ 1 ∧
          (∀ t : ℝ, ∀ y : H, Commute (φ t) y) ∧
          π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))) = φ '' Set.Icc (-1 : ℝ) 1 ∧
          ∃ T W' : Set H, ∃ hQ : LocalNormalSet (φ '' Set.Icc (-1 : ℝ) 1) T,
            ∃ hW'1 : (1 : H) ∈ W', ∃ hW'i : W'⁻¹ = W', ∃ hW'6 : W'^6 ⊆ T,
              IsOpen T ∧ IsOpen W' ∧ LocalGroupTopology (hQ.quotientAlgebra hW'1 hW'i hW'6) ∧
              T2Space (hQ.WindowQuotient hW'1 hW'i hW'6) ∧
              LocallyCompactSpace (hQ.WindowQuotient hW'1 hW'i hW'6) ∧
              ∃ F : LocalGroupHom
                (LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L (fun i => (P i : Set (G i))) D).algebra
                (hQ.quotientAlgebra hW'1 hW'i hW'6),
                ∀ a : (LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L (fun i => (P i : Set (G i))) D).small,
                  F.toFun ((LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L (fun i => (P i : Set (G i))) D).project a) =
                    (hQ.quotientAlgebra hW'1 hW'i hW'6).one ↔ π.toFun a.val ∈ φ '' Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨r,hr0,_,hcurve⟩ := strong_local_connected_central_curve K
  obtain ⟨N,P,φ,hP,hNu,hcont,h0,hadd,h1,hcentral,heq⟩ :=
    hcurve ι U G L hd hr A hA hNSS hne H π V hV hVNSS himage W hWo hW1 hsmall hthick
  have hPA : localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))) ⊆
      localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) :=
    (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) _ _).2
      (Filter.Eventually.of_forall fun i => (hP i).2.2.1)
  have hbound : ∀ t : ℝ, |t| ≤ 1 → φ t ∈ V := by
    intro t ht
    have hm : φ t ∈ π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))) := by
      rw [heq]
      exact ⟨t,abs_le.mp ht,rfl⟩
    obtain ⟨z,hz,he⟩ := hm
    exact he ▸ himage z (hPA hz)
  obtain ⟨T,W',hQ,hW'1,hW'i,hW'6,hTo,hW'o,htop,hT2,hLC⟩ :=
    exists_central_curve_topological_quotient φ hcont h0 hadd h1 hcentral V hVNSS (by norm_num) hbound
  have hPQ : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))),
      π.toFun z ∈ φ '' Set.Icc (-1 : ℝ) 1 := by
    intro z hz
    rw [← heq]
    exact ⟨z,hz,rfl⟩
  obtain ⟨J,η,hJ,hη,D,B,hB,F,hF⟩ := local_central_quotient_model_assembly U G L hd hr A P hK hA hr0
    (fun i => (hP i).2.2.2) π V hV hVNSS himage hQ hW'1 hW'i hW'6 hW'o hPQ
  exact ⟨J,η,N,P,hJ,hη,fun i => ⟨(hP i).1,(hP i).2.1,(hP i).2.2.1⟩,hNu,D,B,hB,
    φ,hcont,h0,hadd,h1,hcentral,heq,T,W',hQ,hW'1,hW'i,hW'6,hTo,hW'o,htop,hT2,hLC,F,hF⟩
end DirectedCycles
