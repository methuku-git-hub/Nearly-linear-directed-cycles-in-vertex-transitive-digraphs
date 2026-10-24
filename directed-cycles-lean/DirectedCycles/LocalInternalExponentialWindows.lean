import DirectedCycles.LocalInternalSymmetricSandwich
import DirectedCycles.LieExponentialBallTopology

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι H E : Type*} [Group H] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] [LieGroup 𝓘(ℝ,E) ∞ H]

/-- The actual internal compact/open sandwich property constructs finite
symmetric source representatives at every sufficiently small exponential
scale. Neither the representatives nor their symmetry is assumed. -/
theorem exists_local_internal_exponential_windows
    (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (W : Set H) (hW : W ∈ 𝓝 (1 : H))
    (hsandwich : ∀ F V : Set H, IsCompact F → IsOpen V → F ⊆ V → V ⊆ W →
      ∃ B : ∀ i, Finset (G i),
        π.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆ π.toFun ⁻¹' V) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R → ∃ A : ∀ i, Finset (G i),
      (∀ i, ∀ x ∈ A i, (L i).inv x ∈ A i) ∧
      π.toFun ⁻¹' ((lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) r) ⊆
        localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) ∧
      localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) ⊆
        π.toFun ⁻¹' ((lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r)) := by
  obtain ⟨R,hR,hball⟩ := lie_exponential_ball_sandwich (E := E) W hW
  refine ⟨R,hR,?_⟩
  intro r hr hrR
  obtain ⟨hc,ho,hsub,hWsub⟩ := hball r hr hrR
  obtain ⟨B,hB⟩ := hsandwich _ _ hc ho hsub hWsub
  exact local_internal_symmetric_sandwich U G L π _ _
    (fun _ hx => lie_exponential_closedBall_inv_mem hx) B hB.1 hB.2
end DirectedCycles
