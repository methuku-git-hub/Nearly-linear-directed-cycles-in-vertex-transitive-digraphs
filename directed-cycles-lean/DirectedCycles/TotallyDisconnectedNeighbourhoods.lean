module

/-
The compact clopen-basis argument below is adapted from mathlib's
Topology/Separation/Profinite.lean, copyright 2017 Johannes Hölzl,
authors Johannes Hölzl and Mario Carneiro, under the Apache 2.0 license.
It is reproduced in this namespace because that optional module is absent
from the pinned compiled dependency cache. The dependency sources are unchanged.
-/
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Function Set Filter Topology TopologicalSpace
namespace DirectedCycles
variable {X : Type*} [TopologicalSpace X]

/-- Compact Hausdorff totally disconnected spaces have a clopen neighbourhood
basis, proved using the compact intersection characterization of components. -/
theorem compact_totallyDisconnected_clopen_basis [T2Space X] [CompactSpace X]
    [TotallyDisconnectedSpace X] (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsClopen s) id := by
  refine ⟨fun U => ?_⟩
  constructor
  · have hx : connectedComponent x = {x} := connectedComponent_eq_singleton x
    rw [connectedComponent_eq_iInter_isClopen] at hx
    intro hU
    let N := {s : Set X // IsClopen s ∧ x ∈ s}
    suffices hex : ∃ s : N, s.val ⊆ U by
      obtain ⟨⟨s,hs,hsx⟩,hsub⟩ := hex
      exact ⟨s,⟨hsx,hs⟩,hsub⟩
    have : Nonempty N := ⟨⟨univ,isClopen_univ,mem_univ x⟩⟩
    have hclosed : ∀ s : N, IsClosed s.val := fun s => s.property.1.1
    have hdir : Directed GE.ge fun s : N => s.val := by
      rintro ⟨s,hs,hxs⟩ ⟨t,ht,hxt⟩
      exact ⟨⟨s ∩ t,hs.inter ht,⟨hxs,hxt⟩⟩,inter_subset_left,inter_subset_right⟩
    have hn : ∀ y ∈ ⋂ s : N, s.val, U ∈ 𝓝 y := by
      intro y hy
      rw [hx,mem_singleton_iff] at hy
      rwa [hy]
    exact exists_subset_nhds_of_compactSpace hdir hclosed (mem_nhdsSet_iff_forall.mpr hn)
  · rintro ⟨V,⟨hxV,hV⟩,hVU⟩
    exact Filter.mem_of_superset (hV.isOpen.mem_nhds hxV) hVU

/-- Every identity neighbourhood in a locally compact Hausdorff totally
disconnected space contains a compact open neighbourhood. -/
theorem exists_compact_open_neighbourhood [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] {x : X} {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ V : Set X, IsCompact V ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨O,hOU,hOo,hxO⟩ := mem_nhds_iff.mp hU
  obtain ⟨s,hsc,hxs,hsO⟩ := exists_compact_subset hOo hxO
  let xs : s := ⟨x,interior_subset hxs⟩
  let u : Set s := Subtype.val ⁻¹' interior s
  have hu : IsOpen u := isOpen_interior.preimage continuous_subtype_val
  let : CompactSpace s := isCompact_iff_compactSpace.1 hsc
  obtain ⟨V,⟨hVx,hVcl⟩,hVu⟩ := (compact_totallyDisconnected_clopen_basis xs).mem_iff.mp
    (hu.mem_nhds hxs)
  change V ⊆ u at hVu
  have hVo : IsOpen ((Subtype.val : s → X) '' V) := by
    let v : Set u := (Subtype.val : u → s) ⁻¹' V
    have he : (fun z : u => (z.val : X)) = (Subtype.val : s → X) ∘ (Subtype.val : u → s) := rfl
    have hf0 : IsEmbedding (fun z : u => (z.val : X)) := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
    have hf1 : IsOpenEmbedding (fun z : u => (z.val : X)) := by
      refine ⟨hf0,?_⟩
      have hr : Set.range (fun z : u => (z.val : X)) = interior s := by
        rw [he,Set.range_comp,Subtype.range_coe,Subtype.image_preimage_coe]
        exact Set.inter_eq_self_of_subset_right interior_subset
      rw [hr]
      exact isOpen_interior
    have hv : IsOpen v := hVcl.isOpen.preimage continuous_subtype_val
    have him : (Subtype.val : s → X) '' V = (fun z : u => (z.val : X)) '' v := by
      rw [he,Set.image_comp,Subtype.image_preimage_coe,Set.inter_eq_self_of_subset_right hVu]
    rw [him]
    exact hf1.isOpenMap v hv
  refine ⟨Subtype.val '' V,hVcl.isClosed.isCompact.image continuous_subtype_val,hVo,?_,?_⟩
  · exact ⟨xs,hVx,rfl⟩
  · rintro y ⟨z,_,rfl⟩
    exact hOU (hsO z.property)
end DirectedCycles
