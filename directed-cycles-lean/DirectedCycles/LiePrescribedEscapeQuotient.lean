import DirectedCycles.LiePrescribedCentralModel
import DirectedCycles.LocalNestedModelEscapeControlledQuotient
import DirectedCycles.LocalCentralQuotientLocalSandwich
import DirectedCycles.LocalComponentProjectedEscapeKernel
import DirectedCycles.LocalModelEscapeControl

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles
variable {ι H E : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] [LieGroup 𝓘(ℝ,E) ∞ H]

/-- The prescribed central quotient windows have uniformly controlled lifts
and NSS finite components. The same source window and descended model occur
in the geometric comparison and in every conclusion. -/
theorem lie_prescribed_escape_controlled_central_model
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
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    {Ra ra : ℝ} (hra : 0 < ra) (hRa : (1001/1000)*ra < Ra)
    (hinj : Set.InjOn (lieExponential (G := H) (E := E)) (Metric.ball 0 Ra))
    (hAo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
      π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000)*ra))
    (hAs : ∀ z, π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) ra →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (φ : ℝ → H) (hφ0 : φ 0 = 1) (hφc : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t)
    (hφform : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u Nu (fun i => 2*Nu i) pu t))
    (V : Set H) (hV : IsCompact V) (hVNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V)
    (U₀ : Set H) (hU₀ : IsOpen U₀) (hU₀1 : (1 : H) ∈ U₀)
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
    {Q T W : Set H} (hQ : LocalNormalSet Q T)
    (hW1 : (1 : H) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ T) (hWo : IsOpen W)
    [T2Space (hQ.WindowQuotient hW1 hWi hW6)]
    (hPeq : π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))) = Q)
    (Vq : Set (hQ.WindowQuotient hW1 hWi hW6))
    (hqNSS : ∀ x, ∀ q : (hQ.quotientAlgebra hW1 hWi hW6).PowerSequence x,
      (∀ n, q.power n ∈ Vq) → x = (hQ.quotientAlgebra hW1 hWi hW6).one)
    (Z : Set H) (hZ : IsCompact Z) (hZ1 : (1 : H) ∈ interior Z) (hZW : Z ⊆ W) (hZU₀ : Z ⊆ U₀)
    (hZVq : ∀ x : W, x.val ∈ Z → hQ.windowMk hW1 hWi hW6 x ∈ Vq) :
    ∃ K : ℕ, ∃ R : ℝ, 1 ≤ K ∧ 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      ∃ B : ∀ i, Finset (G i), ∃ D : ∀ i, (L i).CentralQuotientData (P i : Set (G i)),
      ∃ J : ℕ, 1 ≤ J ∧
        π.toFun ⁻¹' ((lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) r) ⊆
          localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆
          π.toFun ⁻¹' ((lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r)) ∧
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
          (hQ.quotientAlgebra hW1 hWi hW6),
          (∃ hDW : ∀ x ∈ (LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L
              (fun i => (P i : Set (G i))) D).small, π.toFun x ∈ W,
            ∀ hPQ : ∀ p ∈ localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))), π.toFun p ∈ Q,
            Ψ = ((LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L (fun i => (P i : Set (G i))) D).modelQuotientHom
              hQ hW1 hWi hW6 π hPQ hDW).comp (LocalGroupAlgebra.CentralQuotientData.quotientUltraHom
                U G L (fun i => (P i : Set (G i))) D hd hr)) ∧
          (∀ a : ∀ i, (D i).small,
            Ψ.toFun (localUltraMk (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).project (a i))) =
              (hQ.quotientAlgebra hW1 hWi hW6).one →
            π.toFun (localUltraMk (U : Filter ι) G (fun i => (a i).val)) ∈
              π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i)))) ∧
          (∀ z, Ψ.toFun z ∈ Vq) ∧
          (∀ F O : Set (hQ.WindowQuotient hW1 hWi hW6), IsCompact F → IsOpen O → F ⊆ O →
            ∃ S : ∀ i, Finset (D i).Carrier,
              Ψ.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) (fun i => (D i).Carrier) (fun i => (S i : Set (D i).Carrier)) ∧
              localUltraSet (U : Filter ι) (fun i => (D i).Carrier) (fun i => (S i : Set (D i).Carrier)) ⊆ Ψ.toFun ⁻¹' O) ∧
          ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in (U : Filter ι),
            (∀ y ∈ (D i).finiteImage (B i), ∃ x : (D i).small, x.val ∈ B i ∧ (D i).project x = y ∧
              (L i).escapeNorm (B i : Set (G i)) x.val ≤
                C*(D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier) y) ∧
            (D i).algebra.IsNSS ((D i).finiteImage (B i) : Set (D i).Carrier) := by
  obtain ⟨K,R,hK,hR,hwin⟩ := lie_prescribed_central_model (E := E) U G L hd hr A hA π V hV hVNSS himage
    U₀ hU₀ hU₀1 hsmall hsandwich P hτ hP hQ hW1 hWi hW6 hWo hPeq Vq Z hZ hZ1 hZW hZU₀ hZVq
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
      π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000)*(r/ra)*ra) := by
    intro z hz
    rw [mul_assoc, hdr]
    exact Set.image_mono Metric.ball_subset_closedBall (hBout hz)
  have hBs : ∀ z, π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) ((r/ra)*ra) →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) := by
    intro z hz
    rw [hdr] at hz
    exact hBin (Set.image_mono Metric.ball_subset_closedBall hz)
  have hbound := local_escape_controlled_quotient_from_nested_models U G L hd hr A B hA
    (fun i => (hB i).1) (fun i => (hB i).2.1) hANSS u Nu pu hNu2 hup hue hu1 hunorm humin hNu
    π V hV hVNSS himage hra (div_pos hr0 hra) ((div_le_one hra).2 hrra) hRa hinj hAo hAs hBo hBs
    φ hφ0 hφc hφadd hφform (fun i => (P i : Set (G i))) hPexact D hBsmall
    (fun i => (hB i).2.2.2.1 8 (by omega))
    (fun i x hx => hcentral i x ((hB i).2.2.2.2.1 (hBsmall i hx)))
    (hQ.quotientAlgebra hW1 hWi hW6) Ψ hkernel Vq hqNSS (fun z _ => himageq z)
  exact ⟨B,D,J,hJ,hBin,hBout,hB,hstrong,hcard,Ψ,hmap,hkernel,himageq,hsw,hbound⟩
end DirectedCycles
