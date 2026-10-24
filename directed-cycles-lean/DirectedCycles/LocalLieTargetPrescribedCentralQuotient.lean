import DirectedCycles.LocalLieTargetPrescribedWordWindows
import DirectedCycles.LocalPrescribedCentralQuotient

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι H E : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] {Q : LocalGroupAlgebra H} (X : LocalExponentialData (E := E) Q)

/-- Construct central quotient components using the exact internal Lie
ball windows. Their approximate-group constant is uniform over small scales,
all source domains and central relations are proved, and the original source
has uniform density relative to the quotient times the central progression. -/
theorem local_lie_target_prescribed_central_quotient_windows
    (hQ : LocalGroupSmoothness (E := E) Q)
    (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Fintype (G i)]
    (L : ∀ i, LocalGroupAlgebra (G i)) (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Finset (G i)) {Ka : ℕ} (hA : ∀ i, IsLocalFiniteApproximateGroup (L i) Ka (A i))
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (C : Set H) (hC : IsCompact C)
    (hAC : π.toFun '' localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) ⊆ C)
    (W : Set H) (hW : W ∈ 𝓝 Q.one)
    (hsmall : π.toFun ⁻¹' W ⊆ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hsandwich : ∀ F V : Set H, IsCompact F → IsOpen V → F ⊆ V → V ⊆ W →
      ∃ B : ∀ i, Finset (G i),
        π.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆ π.toFun ⁻¹' V)
    (P : ∀ i, Finset (G i)) {τ : ℝ} (hτ : 0 < τ)
    (hP : ∀ i, (L i).CentralLocalSet (P i : Set (G i)) {x | (L i).escapeNorm (A i) x < 1/1001}
      {x | (L i).escapeNorm (A i) x < τ}) :
    ∃ K : ℕ, ∃ R : ℝ, 1 ≤ K ∧ 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      ∃ B : ∀ i, Finset (G i), ∃ D : ∀ i, (L i).CentralQuotientData (P i : Set (G i)),
      ∃ J : ℕ, 1 ≤ J ∧
        π.toFun ⁻¹' (X.chart '' Metric.closedBall (0 : E) r) ⊆
          localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆
          π.toFun ⁻¹' (X.chart '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r)) ∧
        (∀ i, IsLocalFiniteApproximateGroup (L i) K (B i) ∧ B i ⊆ A i ∧
          (D i).small = (L i).wordPower (B i : Set (G i)) 200 ∧
          (∀ n ≤ 200, (L i).wordPower (B i : Set (G i)) n ⊆ (D i).small) ∧
          (D i).small ⊆ {x | (L i).escapeNorm (A i) x < τ} ∧
          IsLocalFiniteApproximateGroup (D i).algebra K ((D i).finiteImage (B i)) ∧
          (D i).algebra.DivisionClosed ∧ (D i).algebra.Reversible) ∧
        (∀ᶠ i in (U : Filter ι), IsStrongLocalFiniteApproximateGroup (L i) K (B i)) ∧
        ∀ᶠ i in (U : Filter ι), (A i).card ≤ J*((D i).finiteImage (B i)).card*(P i).card := by
  obtain ⟨K,R,hK,hR,hwin⟩ := local_lie_target_prescribed_word_windows X hQ U G L hd hr A hA π C hC hAC
    W hW hsmall hsandwich 4800 (lt_min hτ (by norm_num : (0 : ℝ) < 1/1001))
  refine ⟨K,R,hK,hR,?_⟩
  intro r hr0 hrR
  obtain ⟨B,J,hJ,hBin,hBout,hB,hstrong,hcard⟩ := hwin r hr0 hrR
  choose D hDeq hDword hDsmall hDapprox hDdiv hDrev hDcard using fun i =>
    local_central_quotient_of_prescribed_window (L i) (hd i) (hr i) (A i) (P i) (B i)
      (hB i).1 (hP i) (hB i).2.2.1 (hB i).2.2.2
  refine ⟨B,D,J,hJ,hBin,hBout,fun i => ⟨(hB i).1,(hB i).2.1,hDeq i,hDword i,hDsmall i,
    hDapprox i,hDdiv i,hDrev i⟩,hstrong,?_⟩
  filter_upwards [hcard] with i hi
  exact hi.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left J (hDcard i))
end DirectedCycles
