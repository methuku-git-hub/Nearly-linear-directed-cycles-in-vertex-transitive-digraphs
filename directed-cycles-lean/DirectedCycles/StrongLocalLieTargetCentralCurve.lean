module

public import DirectedCycles.StrongLocalCentralSegment
public import DirectedCycles.StrongLocalSelectedCentralSet
public import DirectedCycles.LocalLieTargetLongPowerSegments
public import DirectedCycles.LocalMinimalEscapeUnbounded
public import DirectedCycles.LocalToLocalScaledCurve
public import DirectedCycles.LocalToLocalScaledCentrality
public import DirectedCycles.LocalLieTargetEscapeNeighbourhood
public import DirectedCycles.SmoothLocalCurveNonzeroTangent
public import DirectedCycles.LocalProductDomainTransfer
public import DirectedCycles.LocalToLocalShortProgressionModel

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles

/-- Strong finite NSS source groups over a positive-dimensional smooth local
Lie target construct specified long central segments and a nontrivial smooth
local central curve whose closed unit segment is exactly the image of the
selected progression. All witnesses are retained for the quotient step. -/
theorem strong_local_lie_target_central_curve (K : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ (ι : Type*) (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Fintype (G i)]
        (L : ∀ i, LocalGroupAlgebra (G i))
        (_hd : ∀ i, (L i).DivisionClosed) (_hr : ∀ i, (L i).Reversible)
        (A : ∀ i, Finset (G i)),
        (∀ i, IsStrongLocalFiniteApproximateGroup (L i) K (A i)) →
        (∀ i, (L i).IsNSS (A i : Set (G i))) →
        (∀ i, ∃ g ∈ A i, g ≠ (L i).one) →
        ∀ (H E : Type*) [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
          [CompleteSpace E] [Nontrivial E] [ChartedSpace E H] [IsManifold 𝓘(ℝ,E) ∞ H]
          (Q : LocalGroupAlgebra H) (_hQ : LocalGroupSmoothness (E := E) Q)
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
            ∃ a : OpenPartialHomeomorph E H, (0 : E) ∈ a.source ∧ a 0 = Q.one ∧
              ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a 0 ∧
              ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a.symm Q.one ∧
              ∃ v : E, v ≠ 0 ∧ HasDerivAt (fun t => a.symm (f t)) v 0 := by
  obtain ⟨δ,hδ,hδhalf,hseg⟩ := strong_local_central_segment K
  refine ⟨δ,hδ,hδhalf,?_⟩
  intro ι U G _ L hd hr A hA hNSS hne H E _ _ _ _ _ _ _ Q hQ π V hVNSS htrap himage W hWo hW1 hsmall hthick
  obtain ⟨D⟩ := smooth_local_exponential_data Q hQ
  choose u hu hu1 N hN p hprev hexit hnorm hmin hcent hmem using
    fun i => hseg (G i) (L i) (A i) (hA i) (hd i) (hr i) (hNSS i) (hne i)
  let B : ∀ i, Set (G i) := fun i => (A i : Set (G i))
  let J := localUltraAlgebra (U : Filter ι) G L
  have hB1 : J.one ∈ localUltraSet (U : Filter ι) G B :=
    (localUltraMk_mem_iff (U : Filter ι) G B _).2 (Filter.Eventually.of_forall fun i => (hA i).approximate.one_mem)
  have hBdom : J.AllProductsDefined (localUltraSet (U : Filter ι) G B) 2 :=
    (localUltra_allProductsDefined_iff U G L B 2).2 (Filter.Eventually.of_forall fun i =>
      (hA i).approximate.allProducts.mono (L i) (Set.Subset.refl _) (by omega : 2 ≤ 200))
  have hbin : ∀ x ∈ localUltraSet (U : Filter ι) G B, ∀ y ∈ localUltraSet (U : Filter ι) G B,
      J.Defined x y := by
    intro x hx y hy
    obtain ⟨z,hz⟩ := hBdom [x,y] (by simp) (by aesop)
    exact ⟨z,(LocalGroupAlgebra.Product.pair_iff J x y z).1 hz⟩
  have hsegments := fun k => exists_long_power_segment_of_local_lie_model D J
    (localUltraSet (U : Filter ι) G B) hB1 hbin π W (hWo.mem_nhds hW1) hsmall hthick k
  have hNpos : ∀ᶠ i in (U : Filter ι), 0 < N i := Filter.Eventually.of_forall fun i => by have := hN i; omega
  have hunbounded := local_minimal_first_escape_unbounded U G L B u N hNpos
    (Filter.Eventually.of_forall hnorm) (Filter.Eventually.of_forall hmin) hsegments
  have hM : ∀ᶠ i in (U : Filter ι), 2*N i ≤ 2*N i := Filter.Eventually.of_forall fun _ => le_rfl
  have hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ B i, (L i).inv x ∈ B i :=
    Filter.Eventually.of_forall fun i => (hA i).approximate.inv_mem
  obtain ⟨f,hfc,hf0,hflaw,hf1,hformula⟩ := exists_local_to_local_scaled_curve U G L Q hd hr B u N
    (fun i => 2*N i) p hunbounded hM hi (Filter.Eventually.of_forall hprev)
    (Filter.Eventually.of_forall hexit) π V hVNSS htrap himage W hW1 hsmall
  choose P hPeq hPcard hPA hPlocal using fun i => strong_local_central_set_of_segment (L i)
    (hA i) (hd i) (hr i) (hNSS i) (hu i) (hu1 i) (hN i) (p i) (hprev i) (hexit i) hδhalf (hcent i)
  have himageEq : π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))) =
      f '' Set.Icc (-1 : ℝ) 1 := by
    have he : (fun i => (P i : Set (G i))) = (fun i => (p i).shortSignedSet (N i)) := funext hPeq
    rw [he]
    exact local_to_local_shortProgression_model_image_eq U G L Q hd hr B u N (fun i => 2*N i) p
      hunbounded hM hi (Filter.Eventually.of_forall hprev) π V hVNSS himage f (fun t _ => hformula t)
  refine ⟨u,N,p,P,f,fun i => ⟨hN i,hPcard i,hPA i,hPlocal i⟩,hPeq,
    fun i => ⟨hu i,hu1 i,hprev i,hexit i,hnorm i,hmin i,hcent i,hmem i⟩,hformula,himageEq,hunbounded,hfc,hf0,hflaw,hf1,?_,
    smooth_local_curve_nonzero_tangent Q hQ f hf0 hfc hflaw hf1⟩
  obtain ⟨O,hOo,hO1,hOW,hOsmall⟩ := local_to_local_model_internal_escape_neighbourhood U G L D B
    hB1 hbin π W hWo hW1 hsmall hδ
  let C : ∀ i, Set (G i) := fun i => {x | (L i).escapeNorm (B i) x < δ}
  have hc : ∀ᶠ i in (U : Filter ι), ∀ x ∈ C i, x ∈ B i ∧ (L i).Commute x (u i) := by
    apply Filter.Eventually.of_forall
    intro i x hx
    change (L i).escapeNorm (B i) x < δ at hx
    exact ⟨(L i).mem_of_escapeNorm_lt_one (hA i).approximate.one_mem (by linarith),hcent i x hx⟩
  refine ⟨O,hOo,hO1,local_to_local_scaled_curve_central U G L Q hd B C u N (fun i => 2*N i) p
    ((hunbounded 2).mono fun i hni => ⟨by omega,by omega⟩) (Filter.Eventually.of_forall hu) hi
    (Filter.Eventually.of_forall fun i => (hA i).approximate.allProducts.mono (L i) (Set.Subset.refl _) (by omega : 3 ≤ 200))
    (Filter.Eventually.of_forall hprev) hc π f (fun t _ => hformula t) O ?_⟩
  intro y hy
  obtain ⟨z,hz⟩ := hthick y (hOW hy)
  exact ⟨z,hOsmall z (hz.symm ▸ hy),hz⟩
end DirectedCycles
