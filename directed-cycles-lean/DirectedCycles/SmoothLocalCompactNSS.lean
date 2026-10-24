import DirectedCycles.SmoothLocalGroupNSS
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E G] [IsManifold 𝓘(ℝ,E) ∞ G]

/-- A finite-dimensional smooth local group has compact NSS neighbourhoods
inside every prescribed identity neighbourhood. Uniform finite-power trapping
holds on the same compact neighbourhood. -/
theorem smooth_local_group_compact_nss (L : LocalGroupAlgebra G)
    (hL : LocalGroupSmoothness (E := E) L) {U : Set G} (hU : U ∈ 𝓝 L.one) :
    ∃ V : Set G, V ∈ 𝓝 L.one ∧ IsCompact V ∧ V ⊆ U ∧ L.IsNSS V ∧
      (∀ x : G, ∀ p : L.PowerSequence x, (∀ n, p.power n ∈ V) → x = L.one) ∧
      (∀ W : Set G, W ∈ 𝓝 L.one → ∃ M : ℕ, 1 ≤ M ∧
        ∀ x : G, (∀ n ≤ M, L.PowerIn V x n) → x ∈ W) := by
  let : LocallyCompactSpace G := Manifold.locallyCompact_of_finiteDimensional 𝓘(ℝ,E)
  obtain ⟨S,hS,hNSS,hseq,htrap⟩ := smooth_local_group_nss_neighbourhood L hL
  obtain ⟨V,hV,hsub,hcompact⟩ :=
    LocallyCompactSpace.local_compact_nhds L.one (U ∩ S) (Filter.inter_mem hU hS)
  have hVS : V ⊆ S := fun _ hx => (hsub hx).2
  refine ⟨V,hV,hcompact,fun _ hx => (hsub hx).1,?_,?_,?_⟩
  · exact fun H hH hHV => hNSS H hH (hHV.trans hVS)
  · exact fun x p hp => hseq x p (fun n => hVS (hp n))
  · intro W hW
    obtain ⟨M,hM,hm⟩ := htrap W hW
    refine ⟨M,hM,?_⟩
    intro x hx
    apply hm x
    intro n hn
    obtain ⟨y,hy,hp⟩ := hx n hn
    exact ⟨y,hVS hy,hp⟩
end DirectedCycles
