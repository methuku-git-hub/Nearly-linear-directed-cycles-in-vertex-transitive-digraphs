import DirectedCycles.LieGroupNSS
import DirectedCycles.CompactNSSCurve
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) 1 G] [hfin : FiniteDimensional ℝ E]

include hLie hfin in
/-- Every identity neighbourhood in a finite-dimensional real Lie group
contains a compact identity neighbourhood with no nontrivial trapped cyclic
semigroup. All compactness and NSS inputs are constructed. -/
theorem lieGroup_compact_cyclic_nss {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ V : Set G, V ∈ 𝓝 (1 : G) ∧ IsCompact V ∧ V ⊆ U ∧
      ∀ x : G, (∀ n : ℕ, x^n ∈ V) → x = 1 := by
  let : LocallyCompactSpace G := Manifold.locallyCompact_of_finiteDimensional 𝓘(ℝ,E)
  obtain ⟨W,hW,hcyclic⟩ := lieGroup_cyclic_nss_neighbourhood (G := G) (E := E)
  obtain ⟨V,hV,hsub,hcompact⟩ :=
    LocallyCompactSpace.local_compact_nhds (1 : G) (U ∩ W) (Filter.inter_mem hU hW)
  refine ⟨V,hV,hcompact,fun x hx => (hsub hx).1,?_⟩
  intro x hx
  exact hcyclic x (fun n => (hsub (hx n)).2)

include hLie hfin in
/-- A compact Lie NSS neighbourhood supplies uniform finite power trapping
into every open identity neighbourhood. -/
theorem lieGroup_compact_power_trapping [T2Space G] {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ V : Set G, V ∈ 𝓝 (1 : G) ∧ IsCompact V ∧ V ⊆ U ∧
      ∀ W : Set G, IsOpen W → (1 : G) ∈ W →
        ∃ M : ℕ, 1 ≤ M ∧ ∀ x : G, (∀ n ≤ M, x^n ∈ V) → x ∈ W := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ,E)) (n := 1)
  obtain ⟨V,hV,hcompact,hsub,hcyclic⟩ := lieGroup_compact_cyclic_nss (E := E) hU
  exact ⟨V,hV,hcompact,hsub,fun _ hWo hW1 => compact_power_trapping hcompact hcyclic hWo hW1⟩

include hLie hfin in
/-- In a finite-dimensional real Lie group, boundedness in a constructed
compact NSS neighbourhood forces an algebraic one-parameter map to be continuous. -/
theorem lieGroup_curve_continuity_neighbourhood [T2Space G] :
    ∃ V : Set G, V ∈ 𝓝 (1 : G) ∧ IsCompact V ∧
      ∀ f : ℝ → G, f 0 = 1 → (∀ s t, f (s+t) = f s*f t) →
        ∀ r : ℝ, 0 < r → (∀ t : ℝ, |t| ≤ r → f t ∈ V) → Continuous f := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ,E)) (n := 1)
  obtain ⟨V,hV,hcompact,_,hcyclic⟩ :=
    lieGroup_compact_cyclic_nss (G := G) (E := E) (U := Set.univ) Filter.univ_mem
  exact ⟨V,hV,hcompact,fun f h0 hadd _ hr hb =>
    continuous_curve_of_compact_nss f h0 hadd hcompact hcyclic hr hb⟩
end DirectedCycles
