module

public import DirectedCycles.InternalFiniteSetFamily
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Topology
namespace DirectedCycles

/-- A compact set inside an open set can be sandwiched by an internal
finite set when all translated neighbourhoods are internal. -/
theorem internal_finite_sandwich_of_basis {ι : Type*} (u : Ultrafilter ι)
    (G : ι → Type*) [∀ i, Group (G i)]
    (H : Subgroup (GroupUltraproduct (u : Filter ι) G)) [TopologicalSpace H]
    (R : ℕ → Set H)
    (hbasis : ∀ x : H, (𝓝 x).HasBasis (fun _ : ℕ => True) (fun n => (fun y : H => x*y) '' R n))
    (hR : ∀ n, IsInternalFiniteIn u G H (R n))
    (K U : Set H) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ B : Set H, IsInternalFiniteIn u G H B ∧ K ⊆ B ∧ B ⊆ U := by
  classical
  have hex : ∀ x : H, ∃ n : ℕ, x ∈ K → (fun y : H => x*y) '' R n ⊆ U := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨n,hn,hsub⟩ := (hbasis x).mem_iff.mp (hU.mem_nhds (hKU hx))
      exact ⟨n,fun _ => hsub⟩
    · exact ⟨0,fun h => (hx h).elim⟩
  choose n hn using hex
  let V := fun x : H => (fun y : H => x*y) '' R (n x)
  have hV : ∀ x ∈ K, V x ∈ 𝓝 x := by
    intro x hx
    exact (hbasis x).mem_iff.mpr ⟨n x,trivial,Set.Subset.rfl⟩
  obtain ⟨F,hFK,hcover⟩ := hK.elim_nhds_subcover V hV
  refine ⟨⋃ x ∈ F, V x,?_,hcover,?_⟩
  · exact IsInternalFiniteIn.biUnion_finset F V (fun x _ => (hR (n x)).leftTranslate x)
  · intro y hy
    obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hxF,hyV⟩ := Set.mem_iUnion.mp hx
    exact hn x (hFK x hxF) hyV

/-- Restricting representatives to a prescribed finite internal set makes
componentwise containment literal, without changing the internal subset. -/
theorem IsInternalFiniteIn.restrict {ι : Type*} {u : Ultrafilter ι}
    {G : ι → Type*} [∀ i, Group (G i)] {H : Subgroup (GroupUltraproduct (u : Filter ι) G)}
    {T : Set H} (hT : IsInternalFiniteIn u G H T) (A : ∀ i, Finset (G i))
    (hTA : T ⊆ H.subtype ⁻¹' ultraSet (u : Filter ι) G (fun i => (A i : Set (G i)))) :
    ∃ B : ∀ i, Finset (G i), (∀ i, B i ⊆ A i) ∧
      T = H.subtype ⁻¹' ultraSet (u : Filter ι) G (fun i => (B i : Set (G i))) := by
  classical
  obtain ⟨B,hB⟩ := hT
  refine ⟨fun i => B i ∩ A i,fun i => Finset.inter_subset_right,?_⟩
  simp only [Finset.coe_inter,ultraSet_inter,Set.preimage_inter,← hB,Set.inter_eq_left.mpr hTA]

end DirectedCycles
