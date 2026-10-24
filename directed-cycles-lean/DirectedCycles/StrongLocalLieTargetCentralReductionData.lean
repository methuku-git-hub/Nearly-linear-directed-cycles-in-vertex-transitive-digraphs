import DirectedCycles.StrongLocalLieTargetCentralCurve
import DirectedCycles.LocalToLocalModelCentralImage
import DirectedCycles.SmoothLocalCentralQuotient

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Topology Manifold ContDiff
namespace DirectedCycles

/-- Strong finite NSS source groups over an actual positive-dimensional local
Lie model construct a specified central progression and an actual smooth
local quotient with strictly lower dimension. The central image, closure and
all quotient inputs are derived from the same finite witnesses. -/
theorem strong_local_lie_target_central_reduction_data (K : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ (ι : Type*) (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Fintype (G i)]
        (L : ∀ i, LocalGroupAlgebra (G i))
        (_hd : ∀ i, (L i).DivisionClosed) (_hr : ∀ i, (L i).Reversible)
        (A : ∀ i, Finset (G i)),
        (∀ i, IsStrongLocalFiniteApproximateGroup (L i) K (A i)) →
        (∀ i, (L i).IsNSS (A i : Set (G i))) →
        (∀ i, ∃ g ∈ A i, g ≠ (L i).one) →
        ∀ (H E : Type*) [TopologicalSpace H] [T2Space H] [NormedAddCommGroup E] [NormedSpace ℝ E]
          [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [ChartedSpace E H] [IsManifold 𝓘(ℝ,E) ∞ H]
          (Q : LocalGroupAlgebra H) (_hQ : LocalGroupSmoothness (E := E) Q)
          (_hdQ : Q.DivisionClosed) (_hrQ : Q.Reversible)
          (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q) (V : Set H),
          (∀ x : H, ∀ q : Q.PowerSequence x, (∀ n, q.power n ∈ V) → x = Q.one) →
          (∀ O : Set H, O ∈ 𝓝 Q.one → ∃ n : ℕ, 1 ≤ n ∧
            ∀ x : H, (∀ j ≤ n, Q.PowerIn V x j) → x ∈ O) →
          (∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V) →
          ∀ W : Set H, IsOpen W → Q.one ∈ W →
          (∀ z, π.toFun z ∈ W → z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))) →
          (∀ y ∈ W, ∃ z, π.toFun z = y) →
          ∃ (u : ∀ i, G i) (N : ι → ℕ)
            (p : ∀ i, (L i).PowerSegment (u i) (2*N i)) (P : ∀ i, Finset (G i)) (f : ℝ → H),
            (∀ i, 2 ≤ N i ∧ (P i).card = 2*N i-1 ∧ (P i : Set (G i)) ⊆ A i ∧
              (L i).CentralLocalSet (P i : Set (G i))
                {x | (L i).escapeNorm (A i) x < 1/1001} {x | (L i).escapeNorm (A i) x < δ}) ∧
            (∀ i, (P i : Set (G i)) = (p i).shortSignedSet (N i)) ∧
            (∀ i, u i ∈ A i ∧ u i ≠ (L i).one ∧
              (∀ n < N i, (p i).power n ∈ A i) ∧ (p i).power (N i) ∉ A i ∧
              (L i).escapeNorm (A i) (u i) = 1/(N i : ℝ) ∧
              (∀ v ∈ A i, v ≠ (L i).one → (L i).escapeNorm (A i) (u i) ≤ (L i).escapeNorm (A i) v) ∧
              (∀ x, (L i).escapeNorm (A i) x < δ → (L i).Commute x (u i)) ∧
              (∀ n ≤ 2*N i, (p i).power n ∈ (L i).wordPower (A i : Set (G i)) 4)) ∧
            (∀ t : ℝ, f t = π.toFun (localScaledPower U G L u N (fun i => 2*N i) p t)) ∧
            π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))) =
              f '' Set.Icc (-1 : ℝ) 1 ∧
            (∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i) ∧
            ContinuousAt f 0 ∧ f 0 = Q.one ∧
            (∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t))) ∧ f 1 ≠ Q.one ∧
            (∃ O : Set H, IsOpen O ∧ Q.one ∈ O ∧
              ∀ t : ℝ, |t| ≤ 1/2 → ∀ y ∈ O, Q.Commute (f t) y) ∧
            ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ f 0 ∧
            (∃ a : OpenPartialHomeomorph E H, (0 : E) ∈ a.source ∧ a 0 = Q.one ∧
              ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a 0 ∧
              ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a.symm Q.one ∧
              ∃ v : E, v ≠ 0 ∧ HasDerivAt (fun t => a.symm (f t)) v 0) ∧
            ∃ (v : E) (ℓ : E →L[ℝ] ℝ), v ≠ 0 ∧ ℓ v = 1 ∧
              Module.finrank ℝ ℓ.ker+1 = Module.finrank ℝ E ∧
              ∃ T : Q.CentralQuotientData (f '' Set.Icc (-1 : ℝ) 1), IsOpen T.small ∧
                T.algebra.DivisionClosed ∧ T.algebra.Reversible ∧
                T2Space T.Carrier ∧ LocallyCompactSpace T.Carrier ∧
                ∃ a : OpenPartialHomeomorph (ℝ × ℓ.ker) H, (0 : ℝ × ℓ.ker) ∈ a.source ∧
                  a 0 = Q.one ∧ T.small ⊆ a.target ∧
                  (∀ x y : T.small, T.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2) ∧
                  ∃ cs : ChartedSpace ℓ.ker T.Carrier,
                    letI := cs
                    IsManifold 𝓘(ℝ,ℓ.ker) ∞ T.Carrier ∧ LocalGroupSmoothness (E := ℓ.ker) T.algebra := by
  obtain ⟨δ,hδ,hδhalf,hcurve⟩ := strong_local_lie_target_central_curve K
  refine ⟨δ,hδ,hδhalf,?_⟩
  intro ι U G _ L hd hr A hA hNSS hne H E _ _ _ _ _ _ _ _ _ Q hQ hdQ hrQ π V hVNSS htrap himage W hWo hW1 hsmall hthick
  obtain ⟨u,N,p,P,f,hP,hPeq,hu,hformula,himageEq,hunbounded,hfc,hf0,hflaw,hf1,hcentral,hfs,htangent⟩ :=
    hcurve ι U G L hd hr A hA hNSS hne H E Q hQ π V hVNSS htrap himage W hWo hW1 hsmall hthick
  obtain ⟨D⟩ := smooth_local_exponential_data Q hQ
  let B : ∀ i, Set (G i) := fun i => (A i : Set (G i))
  let Pi : ∀ i, Set (G i) := fun i => (P i : Set (G i))
  let J := localUltraAlgebra (U : Filter ι) G L
  have hB1 : J.one ∈ localUltraSet (U : Filter ι) G B :=
    (localUltraMk_mem_iff (U : Filter ι) G B _).2 (Filter.Eventually.of_forall fun i => (hA i).approximate.one_mem)
  have hBdom : J.AllProductsDefined (localUltraSet (U : Filter ι) G B) 2 :=
    (localUltra_allProductsDefined_iff U G L B 2).2 (Filter.Eventually.of_forall fun i =>
      (hA i).approximate.allProducts.mono (L i) (Set.Subset.refl _) (by omega : 2 ≤ 200))
  have hbin : ∀ x ∈ localUltraSet (U : Filter ι) G B, ∀ y ∈ localUltraSet (U : Filter ι) G B,
      J.Defined x y := by
    intro x hx y hy
    obtain ⟨z,hz⟩ := hBdom [x,y] (by simp only [List.length_cons,List.length_nil]; omega) (by
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl
      · exact hx
      · exact hy)
    exact ⟨z,(LocalGroupAlgebra.Product.pair_iff J x y z).1 hz⟩
  have hPA : ∀ i, Pi i ⊆ B i := fun i => (hP i).2.2.1
  have hPAu : localUltraSet (U : Filter ι) G Pi ⊆ localUltraSet (U : Filter ι) G B := by
    rintro _ ⟨z,hz,rfl⟩
    exact (localUltraMk_mem_iff _ G B z).2 (hz.mono fun i hi => hPA i hi)
  obtain ⟨V',S',hV'o,hV'1,hS'o,hS'1,hCP⟩ := local_to_local_model_central_image U G L D B Pi
    (by norm_num : (0 : ℝ)<1/1001) hδ (fun i => (hP i).2.2.2) hPA hB1 hbin π W hWo hW1 hsmall hthick
  change Q.CentralLocalSet (π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i)))) V' S' at hCP
  rw [himageEq] at hCP
  have hpre : ∀ t : ℝ, |t| ≤ 1 → ∃ z ∈ localUltraSet (U : Filter ι) G B, π.toFun z = f t := by
    intro t ht
    have hm : f t ∈ π.toFun '' localUltraSet (U : Filter ι) G Pi := by
      rw [himageEq]
      exact ⟨t,abs_le.1 ht,rfl⟩
    obtain ⟨z,hz,he⟩ := hm
    exact ⟨z,hPAu hz,he⟩
  have hbound : ∀ t : ℝ, |t| ≤ 1 → f t ∈ V := by
    intro t ht
    obtain ⟨z,hz,he⟩ := hpre t ht
    exact he ▸ himage z hz
  have hdom : ∀ s t : ℝ, |s| ≤ 1 → |t| ≤ 1 → Q.Defined (f s) (f t) := by
    intro s t hs ht
    obtain ⟨x,hx,hxs⟩ := hpre s hs
    obtain ⟨y,hy,hyt⟩ := hpre t ht
    obtain ⟨z,hz⟩ := hbin x hx y hy
    refine ⟨π.toFun z,?_⟩
    simpa only [hxs,hyt] using π.map_mul hz
  refine ⟨u,N,p,P,f,hP,hPeq,hu,hformula,himageEq,hunbounded,hfc,hf0,hflaw,hf1,hcentral,hfs,htangent,?_⟩
  exact exists_smooth_local_central_quotient Q hQ hdQ hrQ f hf0 hfc hflaw hf1 V hVNSS hbound hdom
    V' S' (hV'o.mem_nhds hV'1) (hS'o.mem_nhds hS'1) hCP
end DirectedCycles
