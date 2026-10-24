import DirectedCycles.LocalLeastLiftGeometricContradiction
import DirectedCycles.LocalDoubledFirstExit
import DirectedCycles.LocalQuadrupledFirstExit
import DirectedCycles.LocalComponentLiftAndExitKernel
import DirectedCycles.LocalMinimalLiftKernel
import DirectedCycles.LocalFirstExitOrder
import DirectedCycles.LocalCentralCorrectionContradiction
import DirectedCycles.LieCentralCurveAlignment
import DirectedCycles.LocalNestedEscapeRatio

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Finite (G i)] (L : ∀ i, LocalGroupAlgebra (G i))
variable {H E : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E H]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ H]

include hLie in
/-- A family of least-escape quotient lifts cannot have infinitesimal
quotient/source escape ratio. The actual first-exit segments are constructed
from source NSS, both model-kernel conclusions are derived, and the geometric
correction contradicts finite leastness. Quotient-source NSS is not assumed. -/
theorem local_least_lift_no_infinitesimal_ratio_components
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    {Ka Kb : ℕ} (A B : ∀ i, Finset (G i))
    (hA : ∀ i, IsLocalFiniteApproximateGroup (L i) Ka (A i))
    (hB : ∀ i, IsLocalFiniteApproximateGroup (L i) Kb (B i))
    (hBA : ∀ i, (B i : Set (G i)) ⊆ A i)
    (hANSS : ∀ i, (L i).IsNSS (A i : Set (G i)))
    (u g : ∀ i, G i) (Nu : ι → ℕ)
    (pu : ∀ i, (L i).PowerSegment (u i) (2*Nu i))
    (hNu2 : ∀ i, 2 ≤ Nu i)
    (hup : ∀ i, ∀ n < Nu i, (pu i).power n ∈ A i)
    (hue : ∀ i, (pu i).power (Nu i) ∉ A i)
    (hu : ∀ i, u i ∈ B i) (hg : ∀ i, g i ∈ B i)
    (hu1 : ∀ i, u i ≠ (L i).one) (hg1 : ∀ i, g i ≠ (L i).one)
    (hunorm : ∀ i, (L i).escapeNorm (A i : Set (G i)) (u i) = 1/(Nu i : ℝ))
    (humin : ∀ i, ∀ x ∈ A i, x ≠ (L i).one →
      (L i).escapeNorm (A i : Set (G i)) (u i) ≤ (L i).escapeNorm (A i : Set (G i)) x)
    (hNu : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < Nu i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hV : IsCompact V) (hVNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V)
    {R r δ : ℝ} (hr0 : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : (1001/1000)*r < R)
    (hinj : Set.InjOn (lieExponential (G := H) (E := E)) (Metric.ball 0 R))
    (hAo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
      π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000)*r))
    (hAs : ∀ z, π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) r →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hBo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))),
      π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000)*δ*r))
    (hBs : ∀ z, π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) (δ*r) →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))))
    (φ : ℝ → H) (hφ0 : φ 0 = 1) (hφc : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t)
    (hφform : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u Nu (fun i => 2*Nu i) pu t))
    (P : ∀ i, Set (G i)) (hPeq : ∀ i, P i = (pu i).shortSignedSet (Nu i))
    (D : ∀ i, (L i).CentralQuotientData (P i))
    (hBsmall : ∀ i, (B i : Set (G i)) ⊆ (D i).small)
    (hB8small : ∀ i, (L i).wordPower (B i : Set (G i)) 8 ⊆ (D i).small)
    (hmin : ∀ i, ∀ z : (D i).small, z.val ∈ B i →
      (D i).project z = (D i).project ⟨g i,hBsmall i (hg i)⟩ →
        (L i).escapeNorm (B i : Set (G i)) (g i) ≤ (L i).escapeNorm (B i : Set (G i)) z.val)
    (hgu : ∀ i, (L i).Commute (g i) (u i))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι),
      (D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier)
        ((D i).project ⟨g i,hBsmall i (hg i)⟩) < ε*(L i).escapeNorm (B i : Set (G i)) (g i))
    {T : Type*} (M : LocalGroupAlgebra T)
    (Ψ : LocalGroupHom (localUltraAlgebra (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).algebra)) M)
    (hkernel : ∀ a : ∀ i, (D i).small,
      Ψ.toFun (localUltraMk (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).project (a i))) = M.one →
        π.toFun (localUltraMk (U : Filter ι) G (fun i => (a i).val)) ∈
          π.toFun '' localUltraSet (U : Filter ι) G P)
    (Vq : Set T)
    (hqNSS : ∀ x : T, ∀ q : M.PowerSequence x, (∀ n, q.power n ∈ Vq) → x = M.one)
    (hqimage : ∀ z ∈ localUltraSet (U : Filter ι) (fun i => (D i).Carrier)
        (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier)),
      Ψ.toFun z ∈ Vq) : False := by
  classical
  have hBNSS : ∀ i, (L i).IsNSS (B i : Set (G i)) :=
    fun i S hS hSB => hANSS i S hS (hSB.trans (hBA i))
  choose Ng hNg2 pg hgp hge hgnorm _ using fun i => local_approximate_doubled_first_exit (L i) (hA i)
    (hBA i (hg i)) ((L i).positive_escape_of_finite_nss (hd i) (hr i) (hA i).one_mem (hANSS i) (hg1 i))
  choose Ku hKu2 qu huq hue' _ huq8 using fun i => local_approximate_quadrupled_first_exit (L i) (hB i)
    (hu i) ((L i).positive_escape_of_finite_nss (hd i) (hr i) (hB i).one_mem (hBNSS i) (hu1 i))
  choose Kg hKg2 qg hgq hge' hgnorm' hgq8 using fun i => local_approximate_quadrupled_first_exit (L i) (hB i)
    (hg i) ((L i).positive_escape_of_finite_nss (hd i) (hr i) (hB i).one_mem (hBNSS i) (hg1 i))
  let p : ∀ i, (L i).PowerSegment (g i) (Kg i) := fun i =>
    ⟨(qg i).power,fun n hn => (qg i).product n (by omega)⟩
  have hqone : ∀ i, (D i).algebra.one ∈ (D i).finiteImage (B i) := by
    intro i
    apply Finset.mem_image.mpr
    exact ⟨⟨(L i).one,(D i).one_mem⟩,by simpa only [Finset.mem_subtype] using (hB i).one_mem,
      (D i).projectionHom.map_one⟩
  obtain ⟨hgker,hexitker⟩ := LocalGroupAlgebra.CentralQuotientData.component_projected_negligible_lift_and_exit_kernel
    U G L P D B g Kg p (fun i => hBsmall i (hg i))
    (fun i n hn => hB8small i (hgq8 i n (by omega))) (Filter.Eventually.of_forall hqone)
    (Filter.Eventually.of_forall fun i => by have := hKg2 i; omega) hgnorm' hsmall
    M π Ψ (π.toFun '' localUltraSet (U : Filter ι) G P) hkernel Vq hqNSS hqimage
  have hPA : ∀ i, P i ⊆ A i := by
    intro i x hx
    rw [hPeq i] at hx
    obtain ⟨k,hk,rfl⟩ := hx
    dsimp only [LocalGroupAlgebra.PowerSegment.signedPower]
    split_ifs
    · exact hup i _ hk
    · exact (hA i).inv_mem _ (hup i _ hk)
  have hPi : ∀ i, ∀ x ∈ P i, (L i).inv x ∈ P i := by
    intro i x hx
    rw [hPeq i] at hx ⊢
    obtain ⟨k,hk,rfl⟩ := hx
    exact ⟨-k,by simpa only [Int.natAbs_neg] using hk,(pu i).signedPower_neg k⟩
  have hKg := local_minimal_lift_exit_unbounded_of_kernel U G L hd B P (fun i => (A i : Set (G i))) D g Kg
    (fun i => by have := hKg2 i; omega) hg hBsmall hBA (fun i => (hB i).one_mem)
    (fun i => (hB i).allProducts.mono (L i) (Set.Subset.refl _) (by omega : 2 ≤ 200)) hPA hPi
    (fun i => (hA i).allProducts.mono (L i) (Set.Subset.refl _) (by omega : 2 ≤ 200)) hgnorm' hmin π
    (fun z hz => hBs z ⟨0,by simpa only [Metric.mem_ball,dist_self] using mul_pos hδ hr0,
      lieExponential_zero.trans hz.symm⟩) hgker
  have hPeqmodel : π.toFun '' localUltraSet (U : Filter ι) G P = φ '' Set.Icc (-1 : ℝ) 1 := by
    have he : P = fun i => (pu i).shortSignedSet (Nu i) := funext hPeq
    rw [he]
    exact local_shortProgression_model_image_eq U G L hd hr (fun i => (A i : Set (G i))) u Nu
      (fun i => 2*Nu i) pu hNu (Filter.Eventually.of_forall fun _ => le_rfl)
      (Filter.Eventually.of_forall fun i => (hA i).inv_mem) (Filter.Eventually.of_forall hup)
      π V hVNSS himage φ hφform
  have hendpoint : π.toFun (localUltraMk (U : Filter ι) G (fun i => (qg i).power (Kg i))) ∈
      φ '' Set.Icc (-1 : ℝ) 1 := by
    rw [← hPeqmodel]
    exact hexitker
  have hminouter : ∀ i, 1/(Nu i : ℝ) ≤ 1/(Ng i : ℝ) := by
    intro i
    rw [← hunorm i,← hgnorm i]
    exact humin i _ (hBA i (hg i)) (hg1 i)
  exact local_least_lift_geometric_contradiction U G L hd hr A B hA hB hBA u g Nu Ng Ku Kg pu pg qu qg
    (fun i => ⟨hNu2 i,hNg2 i,hKu2 i,hKg2 i⟩) hup hgp huq hgq hue hge hue' hge' huq8 hgq8 hu hg
    hminouter hNu hKg π V hV hVNSS himage hr0 hδ hδ1 hR hinj hAo hAs hBo hBs
    φ hφ0 hφc hφadd hφform hendpoint P hPeq D hBsmall hmin hgnorm' hgu
end DirectedCycles
