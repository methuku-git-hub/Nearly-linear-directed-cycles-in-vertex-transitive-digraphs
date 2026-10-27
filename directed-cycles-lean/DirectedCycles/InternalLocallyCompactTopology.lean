module

public import DirectedCycles.ApproximateRootChains
public import DirectedCycles.UltraproductFiniteCovers
public import DirectedCycles.InternalTranslateSaturation
public import DirectedCycles.ShrinkingTopologyCompactness
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Pointwise

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Pointwise Topology
namespace DirectedCycles
namespace ApproximateRootChain
variable {G : ℕ → Type*} [∀ i, Group (G i)]
variable {A : ∀ i, Finset (G i)} (C : ApproximateRootChain G A)

@[instance_reducible]
def modelBasis (u : Ultrafilter ℕ) (hAone : ∀ i, 1 ∈ A i)
    (hAi : ∀ i, (A i : Set (G i))⁻¹ = (A i : Set (G i))) :
    GroupFilterBasis (Subgroup.closure (ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i))))) :=
  (C.shrinking (u : Filter ℕ) hAone).subgroupFilterBasis _ (C.shrinking_conjugation u hAone hAi)

/-- The internal fourth power is compact in the actual topology on the
generated subgroup. The finite covers and saturation hypotheses are fully
supplied by the finite normal-neighbourhood construction. -/
theorem compact_fourth_power (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ Filter.atTop)
    (K : ℝ) (hA : ∀ i, IsApproximateSubgroup K (A i : Set (G i))) :
    let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
    let H := Subgroup.closure B
    @IsCompact H (C.modelBasis u (fun i => (hA i).one_mem) (fun i => (hA i).inv_eq_self)).topology
      (H.subtype ⁻¹' (B^4)) := by
  classical
  let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
  let H := Subgroup.closure B
  let S := C.shrinking (u : Filter ℕ) (fun i => (hA i).one_mem)
  have hH := C.shrinking_conjugation u (fun i => (hA i).one_mem) (fun i => (hA i).inv_eq_self)
  have hBH : B^4 ⊆ H := Subgroup.pow_subset Subgroup.subset_closure
  apply S.subgroup_compact_of_covers H hH (H.subtype ⁻¹' (B^4))
  · intro n
    have hRshort : ∀ i, C.roots n i ⊆ A i^16 := by
      intro i
      have hsub : (C.roots n i : Set (G i)) ⊆ (A i : Set (G i))^4 :=
        (Set.subset_pow (C.approximate n i).one_mem (by omega : 4 ≠ 0)).trans (C.fourth_subset n i)
      have hh := hsub.trans (Set.pow_subset_pow_right (hA i).one_mem (by omega : 4 ≤ 16))
      exact_mod_cast hh
    have hRi : ∀ i, (C.roots n i)⁻¹ = C.roots n i := by
      intro i
      apply Finset.coe_injective
      simpa only [Finset.coe_inv] using (C.approximate n i).inv_eq_self
    obtain ⟨F,hFB,hcover⟩ := ultra_finite_power_cover u G A (C.roots n) K (C.density n) 4 hA
      (C.density_pos n) hRshort (C.dense n) (fun i => (C.approximate n i).one_mem) hRi
    have hSH : S.sets n ⊆ H := (C.shrinking_subset _ _ n).trans hBH
    exact finite_translate_cover_subgroup H (B^4) (S.sets n) hSH F (hFB.trans hBH) hcover
  · intro c hfinite
    have hTH : ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i))^4) ⊆ H := by
      simpa only [ultraSet_pow] using hBH
    have hs := internal_subgroup_translate_saturation u hu G H
      (fun i => (A i : Set (G i))^4) (fun n i => (C.roots n i : Set (G i))^4) hTH c
      (by simpa only [ultraSet_pow,B,S,shrinking,internalShrinkingNeighbourhoods,Set.mem_preimage,Subgroup.coe_subtype] using hfinite)
    simpa only [ultraSet_pow,B,S,shrinking,internalShrinkingNeighbourhoods,Set.mem_preimage,Subgroup.coe_subtype] using hs

/-- This constructs a locally compact group topology. Hausdorff separation
and the Lie-model requirements are separate subsequent obligations. -/
theorem model_locallyCompact (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ Filter.atTop)
    (K : ℝ) (hA : ∀ i, IsApproximateSubgroup K (A i : Set (G i))) :
    let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
    let H := Subgroup.closure B
    @LocallyCompactSpace H
      (C.modelBasis u (fun i => (hA i).one_mem) (fun i => (hA i).inv_eq_self)).topology := by
  let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
  let H := Subgroup.closure B
  let basis := C.modelBasis u (fun i => (hA i).one_mem) (fun i => (hA i).inv_eq_self)
  let : TopologicalSpace H := basis.topology
  let : IsTopologicalGroup H := basis.isTopologicalGroup
  have hc : IsCompact (H.subtype ⁻¹' (B^4)) := C.compact_fourth_power u hu K hA
  apply hc.locallyCompactSpace_of_mem_nhds_of_group (x := 1)
  have hn : (H.subtype ⁻¹' (C.shrinking (u : Filter ℕ) (fun i => (hA i).one_mem)).sets 0) ∈ 𝓝 (1 : H) :=
    basis.mem_nhds_one ⟨0,rfl⟩
  exact Filter.mem_of_superset hn (fun x hx => C.shrinking_subset (u : Filter ℕ) (fun i => (hA i).one_mem) 0 hx)

end ApproximateRootChain
end DirectedCycles
