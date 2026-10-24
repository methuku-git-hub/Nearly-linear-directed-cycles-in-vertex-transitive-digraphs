import DirectedCycles.LocalLieTargetUniformMinimalLiftEscape
import DirectedCycles.LocalQuotientEscapeControlledLifts

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Finite (G i)] (L : ∀ i, LocalGroupAlgebra (G i))
variable {H E : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E H]
    {Q : LocalGroupAlgebra H} (Y : LocalExponentialData (E := E) Q)

/-- The compatible-model lifting construction gives a uniform bound for
actual lifts and proves NSS of the finite quotient components. This is the
finite conclusion required by the dimension-reduction step. -/
theorem local_lie_target_uniform_escape_controlled_quotient
    (hQ : LocalGroupSmoothness (E := E) Q)
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    {Ka Kb : ℕ} (A B : ∀ i, Finset (G i))
    (hA : ∀ i, IsLocalFiniteApproximateGroup (L i) Ka (A i))
    (hB : ∀ i, IsLocalFiniteApproximateGroup (L i) Kb (B i))
    (hBA : ∀ i, (B i : Set (G i)) ⊆ A i)
    (hANSS : ∀ i, (L i).IsNSS (A i : Set (G i)))
    (u : ∀ i, G i) (Nu : ι → ℕ)
    (pu : ∀ i, (L i).PowerSegment (u i) (2*Nu i))
    (hNu2 : ∀ i, 2 ≤ Nu i)
    (hup : ∀ i, ∀ n < Nu i, (pu i).power n ∈ A i)
    (hue : ∀ i, (pu i).power (Nu i) ∉ A i)
    (hu : ∀ i, u i ∈ B i)
    (hu1 : ∀ i, u i ≠ (L i).one)
    (hunorm : ∀ i, (L i).escapeNorm (A i : Set (G i)) (u i) = 1/(Nu i : ℝ))
    (humin : ∀ i, ∀ x ∈ A i, x ≠ (L i).one →
      (L i).escapeNorm (A i : Set (G i)) (u i) ≤ (L i).escapeNorm (A i : Set (G i)) x)
    (hNu : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < Nu i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (V : Set H)
    (htrap : ∀ O : Set H, O ∈ 𝓝 Q.one → ∃ k : ℕ, 1 ≤ k ∧
      ∀ x : H, (∀ n ≤ k, Q.PowerIn V x n) → x ∈ O) (hVNSS : ∀ x : H, ∀ q : Q.PowerSequence x, (∀ n, q.power n ∈ V) → x = Q.one)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V)
    {r δ : ℝ} (hr0 : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 10*r < Y.radius)
    (hAo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
      π.toFun z ∈ Y.chart '' Metric.closedBall (0 : E) ((1001/1000)*r))
    (hAs : ∀ z, π.toFun z ∈ Y.chart '' Metric.ball (0 : E) r →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hBo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))),
      π.toFun z ∈ Y.chart '' Metric.closedBall (0 : E) ((1001/1000)*δ*r))
    (hBs : ∀ z, π.toFun z ∈ Y.chart '' Metric.ball (0 : E) (δ*r) →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))))
    (φ : ℝ → H) (hφ0 : φ 0 = Q.one) (hφc : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (φ s) (φ t) (φ (s+t)))
    (hφform : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u Nu (fun i => 2*Nu i) pu t))
    (P : ∀ i, Set (G i)) (hPeq : ∀ i, P i = (pu i).shortSignedSet (Nu i))
    (D : ∀ i, (L i).CentralQuotientData (P i))
    (hBsmall : ∀ i, (B i : Set (G i)) ⊆ (D i).small)
    (hB8small : ∀ i, (L i).wordPower (B i : Set (G i)) 8 ⊆ (D i).small)
    (hcentral : ∀ i, ∀ x ∈ B i, (L i).Commute x (u i))
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
      Ψ.toFun z ∈ Vq) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in (U : Filter ι),
      (∀ y ∈ (D i).finiteImage (B i), ∃ x : (D i).small, x.val ∈ B i ∧ (D i).project x = y ∧
        (L i).escapeNorm (B i : Set (G i)) x.val ≤
          C*(D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier) y) ∧
      (D i).algebra.IsNSS ((D i).finiteImage (B i) : Set (D i).Carrier) := by
  obtain ⟨C,hC,hbound⟩ := local_lie_target_uniform_minimal_lift_escape_bound U G L Y hQ hd hr A B hA hB hBA hANSS
    u Nu pu hNu2 hup hue hu hu1 hunorm humin hNu π V htrap hVNSS himage hr0 hδ hδ1 hR hAo hAs hBo hBs
    φ hφ0 hφc hφadd hφform P hPeq D hBsmall hB8small hcentral M Ψ hkernel Vq hqNSS hqimage
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with i hi
  have hlift := (D i).escape_controlled_lifts_of_minimal_bound (B i) hi
  exact ⟨hlift,(D i).nss_of_escape_controlled_lifts (hd i) (hr i) (B i) (hB i).one_mem
    (fun S hS hSB => hANSS i S hS (hSB.trans (hBA i))) hlift⟩
end DirectedCycles
