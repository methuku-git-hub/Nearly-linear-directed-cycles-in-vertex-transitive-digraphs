module

public import DirectedCycles.LocalLieTargetPrescribedCentralModel
public import DirectedCycles.LocalLieTargetNestedModelEscapeControlledQuotient
public import DirectedCycles.LocalCentralQuotientLocalSandwich
public import DirectedCycles.LocalComponentProjectedEscapeKernel
public import DirectedCycles.LocalModelEscapeControl

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles
variable {ι H E : Type*} [TopologicalSpace H] [T2Space H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] {M : LocalGroupAlgebra H} (Y : LocalExponentialData (E := E) M)

/-- The prescribed central quotient windows have uniformly controlled lifts
and NSS finite components. The same source window and descended model occur
in the geometric comparison and in every conclusion. -/
theorem local_lie_target_prescribed_escape_controlled_central_model
    (hM : LocalGroupSmoothness (E := E) M)
    (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Fintype (G i)]
    (L : ∀ i, LocalGroupAlgebra (G i)) (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Finset (G i)) {Ka : ℕ} (hA : ∀ i, IsLocalFiniteApproximateGroup (L i) Ka (A i))
    (hANSS : ∀ i, (L i).IsNSS (A i : Set (G i)))
    (u : ∀ i, G i) (Nu : ι → ℕ) (pu : ∀ i, (L i).PowerSegment (u i) (2*Nu i))
    (hNu2 : ∀ i, 2 ≤ Nu i)
    (hup : ∀ i, ∀ n < Nu i, (pu i).power n ∈ A i)
    (hue : ∀ i, (pu i).power (Nu i) ∉ A i)
    (hu1 : ∀ i, u i ≠ (L i).one)
    (hunorm : ∀ i, (L i).escapeNorm (A i : Set (G i)) (u i) = 1/(Nu i : ℝ))
    (humin : ∀ i, ∀ x ∈ A i, x ≠ (L i).one →
      (L i).escapeNorm (A i : Set (G i)) (u i) ≤ (L i).escapeNorm (A i : Set (G i)) x)
    (hNu : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < Nu i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) M)
    {ra : ℝ} (hra : 0 < ra) (hRa : 10*ra < Y.radius)
    (hAo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
      π.toFun z ∈ Y.chart '' Metric.closedBall (0 : E) ((1001/1000)*ra))
    (hAs : ∀ z, π.toFun z ∈ Y.chart '' Metric.ball (0 : E) ra →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (φ : ℝ → H) (hφ0 : φ 0 = M.one) (hφc : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → M.mulRel (φ s) (φ t) (φ (s+t)))
    (hφform : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u Nu (fun i => 2*Nu i) pu t))
    (V : Set H) (hV : IsCompact V) (hVNSS : ∀ x : H, ∀ q : M.PowerSequence x, (∀ n, q.power n ∈ V) → x = M.one)
    (htrap : ∀ O : Set H, O ∈ 𝓝 M.one → ∃ n : ℕ, 1 ≤ n ∧
      ∀ x : H, (∀ j ≤ n, M.PowerIn V x j) → x ∈ O)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V)
    (U₀ : Set H) (hU₀ : IsOpen U₀) (hU₀1 : M.one ∈ U₀)
    (hsmall : π.toFun ⁻¹' U₀ ⊆ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hsandwich : ∀ F O : Set H, IsCompact F → IsOpen O → F ⊆ O → O ⊆ U₀ →
      ∃ B : ∀ i, Finset (G i),
        π.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆ π.toFun ⁻¹' O)
    (P : ∀ i, Finset (G i)) {τ : ℝ} (hτ : 0 < τ)
    (hP : ∀ i, (L i).CentralLocalSet (P i : Set (G i)) {x | (L i).escapeNorm (A i) x < 1/1001}
      {x | (L i).escapeNorm (A i) x < τ})
    (hPexact : ∀ i, (P i : Set (G i)) = (pu i).shortSignedSet (Nu i))
    (hcentral : ∀ i, ∀ x, (L i).escapeNorm (A i) x < τ → (L i).Commute x (u i))
    {Q : Set H} (T : M.CentralQuotientData Q) (hWo : IsOpen T.small)
    [T2Space T.Carrier]
    (hPeq : π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))) = Q)
    (Vq : Set T.Carrier)
    (hqNSS : ∀ x, ∀ q : T.algebra.PowerSequence x,
      (∀ n, q.power n ∈ Vq) → x = T.algebra.one)
    (Z : Set H) (hZ : IsCompact Z) (hZ1 : M.one ∈ interior Z) (hZW : Z ⊆ T.small) (hZU₀ : Z ⊆ U₀)
    (hZVq : ∀ x : T.small, x.val ∈ Z → T.project x ∈ Vq) :
    ∃ K : ℕ, ∃ R : ℝ, 1 ≤ K ∧ 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      ∃ B : ∀ i, Finset (G i), ∃ D : ∀ i, (L i).CentralQuotientData (P i : Set (G i)),
      ∃ J : ℕ, 1 ≤ J ∧
        π.toFun ⁻¹' (Y.chart '' Metric.closedBall (0 : E) r) ⊆
          localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆
          π.toFun ⁻¹' (Y.chart '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r)) ∧
        (∀ i, IsLocalFiniteApproximateGroup (L i) K (B i) ∧ B i ⊆ A i ∧
          (D i).small = (L i).wordPower (B i : Set (G i)) 200 ∧
          (∀ n ≤ 200, (L i).wordPower (B i : Set (G i)) n ⊆ (D i).small) ∧
          (D i).small ⊆ {x | (L i).escapeNorm (A i) x < τ} ∧
          IsLocalFiniteApproximateGroup (D i).algebra K ((D i).finiteImage (B i)) ∧
          (D i).algebra.DivisionClosed ∧ (D i).algebra.Reversible) ∧
        (∀ᶠ i in (U : Filter ι), IsStrongLocalFiniteApproximateGroup (L i) K (B i)) ∧
        (∀ᶠ i in (U : Filter ι), (A i).card ≤ J*((D i).finiteImage (B i)).card*(P i).card) ∧
        ∃ Ψ : LocalGroupHom
          (localUltraAlgebra (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).algebra))
          T.algebra,
          (∃ hDW : ∀ x ∈ (LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L
              (fun i => (P i : Set (G i))) D).small, π.toFun x ∈ T.small,
            ∀ hPQ : ∀ p ∈ localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))), π.toFun p ∈ Q,
            Ψ = ((LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L (fun i => (P i : Set (G i))) D).localModelQuotientHom
              T π hPQ hDW).comp (LocalGroupAlgebra.CentralQuotientData.quotientUltraHom
                U G L (fun i => (P i : Set (G i))) D hd hr)) ∧
          (∀ a : ∀ i, (D i).small,
            Ψ.toFun (localUltraMk (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).project (a i))) =
              T.algebra.one →
            π.toFun (localUltraMk (U : Filter ι) G (fun i => (a i).val)) ∈
              π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i)))) ∧
          (∀ z, Ψ.toFun z ∈ Vq) ∧
          (∀ F O : Set T.Carrier, IsCompact F → IsOpen O → F ⊆ O →
            ∃ S : ∀ i, Finset (D i).Carrier,
              Ψ.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) (fun i => (D i).Carrier) (fun i => (S i : Set (D i).Carrier)) ∧
              localUltraSet (U : Filter ι) (fun i => (D i).Carrier) (fun i => (S i : Set (D i).Carrier)) ⊆ Ψ.toFun ⁻¹' O) ∧
          ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in (U : Filter ι),
            (∀ y ∈ (D i).finiteImage (B i), ∃ x : (D i).small, x.val ∈ B i ∧ (D i).project x = y ∧
              (L i).escapeNorm (B i : Set (G i)) x.val ≤
                C*(D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier) y) ∧
            (D i).algebra.IsNSS ((D i).finiteImage (B i) : Set (D i).Carrier) := by
  obtain ⟨K,R,hK,hR,hwin⟩ := local_lie_target_prescribed_central_model Y hM U G L hd hr A hA π V hV htrap himage
    U₀ hU₀ hU₀1 hsmall hsandwich P hτ hP T hWo hPeq Vq Z hZ hZ1 hZW hZU₀ hZVq
  refine ⟨K,min R ra,hK,lt_min hR hra,?_⟩
  intro r hr0 hrR
  obtain ⟨B,D,J,hJ,hBin,hBout,hB,hstrong,hcard,Ψ,hmap,hkernel,himageq,hsw⟩ := hwin r hr0 (hrR.trans_le (min_le_left _ _))
  have hrra : r ≤ ra := (hrR.trans_le (min_le_right _ _)).le
  have hdr : (r/ra)*ra = r := div_mul_cancel₀ r (ne_of_gt hra)
  have hBsmall : ∀ i, (B i : Set (G i)) ⊆ (D i).small := by
    intro i
    rw [← (L i).wordPower_one (B i : Set (G i))]
    exact (hB i).2.2.2.1 1 (by omega)
  have hBo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))),
      π.toFun z ∈ Y.chart '' Metric.closedBall (0 : E) ((1001/1000)*(r/ra)*ra) := by
    intro z hz
    rw [mul_assoc, hdr]
    exact Set.image_mono Metric.ball_subset_closedBall (hBout hz)
  have hBs : ∀ z, π.toFun z ∈ Y.chart '' Metric.ball (0 : E) ((r/ra)*ra) →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) := by
    intro z hz
    rw [hdr] at hz
    exact hBin (Set.image_mono Metric.ball_subset_closedBall hz)
  have hbound := local_lie_target_escape_controlled_quotient_from_nested_models U G L Y hM hd hr A B hA
    (fun i => (hB i).1) (fun i => (hB i).2.1) hANSS u Nu pu hNu2 hup hue hu1 hunorm humin hNu
    π V htrap hVNSS himage hra (div_pos hr0 hra) ((div_le_one hra).2 hrra) hRa hAo hAs hBo hBs
    φ hφ0 hφc hφadd hφform (fun i => (P i : Set (G i))) hPexact D hBsmall
    (fun i => (hB i).2.2.2.1 8 (by omega))
    (fun i x hx => hcentral i x ((hB i).2.2.2.2.1 (hBsmall i hx)))
    T.algebra Ψ hkernel Vq hqNSS (fun z _ => himageq z)
  exact ⟨B,D,J,hJ,hBin,hBout,hB,hstrong,hcard,Ψ,hmap,hkernel,himageq,hsw,hbound⟩
end DirectedCycles
