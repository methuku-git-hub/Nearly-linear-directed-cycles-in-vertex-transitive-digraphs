module

public import DirectedCycles.CountableGroupMetrizability
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
public import Mathlib.Topology.Algebra.Group.Pointwise

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Topology
namespace DirectedCycles
universe u

/-- A genuine Hausdorff metrizable locally compact group and a quotient
map adapted to a specified compact identity neighbourhood. Existence is a
proved construction below, not a structural assumption. -/
structure LocallyCompactGroupModel (H : Type u) [Group H] (T : Set H) where
  carrier : Type u
  group : Group carrier
  topology : TopologicalSpace carrier
  topologicalGroup : @IsTopologicalGroup carrier topology group
  hausdorff : @T2Space carrier topology
  locallyCompact : @LocallyCompactSpace carrier topology
  metrizable : @TopologicalSpace.MetrizableSpace carrier topology
  map : @MonoidHom H carrier _ group.toMulOne
  surjective : Function.Surjective map
  compact_image : @IsCompact carrier topology (map '' T)
  image_nhds : map '' T ∈ @nhds carrier topology (1 : carrier)
  small_preimage : ∃ U ∈ @nhds carrier topology (1 : carrier), map ⁻¹' U ⊆ T

attribute [instance] LocallyCompactGroupModel.group LocallyCompactGroupModel.topology
  LocallyCompactGroupModel.topologicalGroup LocallyCompactGroupModel.hausdorff
  LocallyCompactGroupModel.locallyCompact LocallyCompactGroupModel.metrizable

/-- The separation quotient supplies the Hausdorff and metric model,
while preserving compactness and a small inverse-image neighbourhood. -/
theorem exists_separated_locallyCompact_model {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [(𝓝 (1 : H)).IsCountablyGenerated]
    (T : Set H) (hT : IsCompact T) (hTn : T ∈ 𝓝 (1 : H)) :
    Nonempty (LocallyCompactGroupModel H T) := by
  classical
  let Q := SeparationQuotient H
  let : LocallyCompactSpace H := hT.locallyCompactSpace_of_mem_nhds_of_group hTn
  let : LocallyCompactSpace Q := SeparationQuotient.isOpenQuotientMap_mk.locallyCompactSpace
  let : (𝓝 (1 : Q)).IsCountablyGenerated := by
    rw [← SeparationQuotient.mk_one,← SeparationQuotient.map_mk_nhds]
    exact Filter.map.isCountablyGenerated _ _
  let : TopologicalSpace.MetrizableSpace Q := group_metrizable_of_countable_nhds
  let q : H →* Q := SeparationQuotient.mkMonoidHom
  have hqn : q '' T ∈ 𝓝 (1 : Q) := by
    change SeparationQuotient.mk '' T ∈ 𝓝 (SeparationQuotient.mk (1 : H))
    exact SeparationQuotient.isOpenMap_mk.image_mem_nhds hTn
  have hsmall : ∃ U ∈ 𝓝 (1 : Q), q ⁻¹' U ⊆ T := by
    obtain ⟨V,hVT,hVo,hV1⟩ := mem_nhds_iff.mp hTn
    refine ⟨q '' V,?_,?_⟩
    · exact (SeparationQuotient.isOpenMap_mk _ hVo).mem_nhds ⟨1,hV1,map_one q⟩
    · change SeparationQuotient.mk ⁻¹' (SeparationQuotient.mk '' V) ⊆ T
      rw [SeparationQuotient.preimage_image_mk_open hVo]
      exact hVT
  exact ⟨⟨Q,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    q,SeparationQuotient.surjective_mk,hT.image SeparationQuotient.continuous_mk,hqn,hsmall⟩⟩

end DirectedCycles
