import DirectedCycles.SmoothLocalCompactNSS
import DirectedCycles.LocalToLocalModelEscapeControl

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {H E : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] [IsManifold 𝓘(ℝ,E) ∞ H]

/-- A smooth local Lie target itself supplies the compact NSS window and
finite-power trapping needed to control ultraproduct escape sublevels. -/
theorem smooth_local_model_escape_control (M : LocalGroupAlgebra H)
    (hM : LocalGroupSmoothness (E := E) M) {O : Set H} (hO : O ∈ 𝓝 M.one) :
    ∃ V : Set H, V ∈ 𝓝 M.one ∧ IsCompact V ∧ V ⊆ O ∧ M.IsNSS V ∧
      ∀ (ι : Type*) (U : Ultrafilter ι) (G : ι → Type*)
        (L : ∀ i, LocalGroupAlgebra (G i)) (A : ∀ i, Set (G i)),
        (∀ᶠ i in (U : Filter ι), (L i).one ∈ A i) →
        ∀ π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) M,
          (∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V) →
          ∀ W : Set H, W ∈ 𝓝 M.one →
            ∃ r : ℝ, 0 < r ∧ ∀ z ∈ localUltraSet (U : Filter ι) G
              (fun i => {x | (L i).escapeNorm (A i) x < r}), π.toFun z ∈ W := by
  obtain ⟨V,hV,hcompact,hsub,hNSS,_,htrap⟩ := smooth_local_group_compact_nss M hM hO
  refine ⟨V,hV,hcompact,hsub,hNSS,?_⟩
  intro ι U G L A hA π himage W hW
  exact local_to_local_model_escape_sublevel_small U G L M A hA π V htrap himage W hW
end DirectedCycles
