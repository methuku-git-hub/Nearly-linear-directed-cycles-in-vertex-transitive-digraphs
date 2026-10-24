import DirectedCycles.LocalToLocalInternalSymmetricSandwich
import DirectedCycles.LocalExponentialBallTopology

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι H E : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] {M : LocalGroupAlgebra H} (D : LocalExponentialData (E := E) M)

/-- The actual internal compact/open sandwich property constructs finite
symmetric source representatives at every sufficiently small exponential
scale. Neither the representatives nor their symmetry is assumed. -/
theorem exists_local_to_local_internal_exponential_windows
    (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) M)
    (W : Set H) (hW : W ∈ 𝓝 M.one)
    (hsandwich : ∀ F V : Set H, IsCompact F → IsOpen V → F ⊆ V → V ⊆ W →
      ∃ B : ∀ i, Finset (G i),
        π.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆ π.toFun ⁻¹' V) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R → ∃ A : ∀ i, Finset (G i),
      (∀ i, ∀ x ∈ A i, (L i).inv x ∈ A i) ∧
      π.toFun ⁻¹' (D.chart '' Metric.closedBall (0 : E) r) ⊆
        localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) ∧
      localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) ⊆
        π.toFun ⁻¹' (D.chart '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r)) := by
  obtain ⟨R,hR,hball⟩ := D.ball_sandwich W hW
  refine ⟨R,hR,?_⟩
  intro r hr hrR
  obtain ⟨hc,ho,hsub,hWsub,hi⟩ := hball r hr hrR
  obtain ⟨B,hB⟩ := hsandwich _ _ hc ho hsub hWsub
  exact local_to_local_internal_symmetric_sandwich U G L M π _ _
    hi B hB.1 hB.2
end DirectedCycles
