import DirectedCycles.SeparatedLocallyCompactModel
import DirectedCycles.InternalSetSandwich

set_option autoImplicit false
open Filter
open scoped Topology
namespace DirectedCycles
universe u

/-- A global good-model record including the internal approximation
property, in addition to the genuine locally compact group structure. -/
structure InternalLocallyCompactGroupModel (H : Type u) [Group H] (T : Set H)
    (Internal : Set H → Prop) extends LocallyCompactGroupModel H T where
  neighbourhood : Set carrier
  open_neighbourhood : @IsOpen carrier topology neighbourhood
  one_mem_neighbourhood : (1 : carrier) ∈ neighbourhood
  small_neighbourhood : map ⁻¹' neighbourhood ⊆ T
  thick_neighbourhood : neighbourhood ⊆ map '' T
  internal_sandwich : ∀ F U : Set carrier,
    @IsCompact carrier topology F → @IsOpen carrier topology U → F ⊆ U → U ⊆ neighbourhood →
    ∃ B : Set H, Internal B ∧ map ⁻¹' F ⊆ B ∧ B ⊆ map ⁻¹' U

theorem exists_internal_separated_model {ι : Type*} (u : Ultrafilter ι)
    (G : ι → Type*) [∀ i, Group (G i)]
    (H : Subgroup (GroupUltraproduct (u : Filter ι) G)) [TopologicalSpace H] [IsTopologicalGroup H]
    (T : Set H) (hT : IsCompact T) (hTn : T ∈ 𝓝 (1 : H))
    (R : ℕ → Set H)
    (hbasis : ∀ x : H, (𝓝 x).HasBasis (fun _ : ℕ => True) (fun n => (fun y : H => x*y) '' R n))
    (hR : ∀ n, IsInternalFiniteIn u G H (R n)) :
    Nonempty (InternalLocallyCompactGroupModel H T (IsInternalFiniteIn u G H)) := by
  classical
  let Q := SeparationQuotient H
  let : LocallyCompactSpace H := hT.locallyCompactSpace_of_mem_nhds_of_group hTn
  let : LocallyCompactSpace Q := SeparationQuotient.isOpenQuotientMap_mk.locallyCompactSpace
  let : (𝓝 (1 : H)).IsCountablyGenerated := (hbasis 1).isCountablyGenerated
  let : (𝓝 (1 : Q)).IsCountablyGenerated := by
    rw [← SeparationQuotient.mk_one,← SeparationQuotient.map_mk_nhds]
    exact Filter.map.isCountablyGenerated _ _
  let : TopologicalSpace.MetrizableSpace Q := group_metrizable_of_countable_nhds
  let q : H →* Q := SeparationQuotient.mkMonoidHom
  obtain ⟨V,hVT,hVo,hV1⟩ := mem_nhds_iff.mp hTn
  let U₀ := q '' V
  have hUo : IsOpen U₀ := SeparationQuotient.isOpenMap_mk V hVo
  have hU1 : (1 : Q) ∈ U₀ := ⟨1,hV1,map_one q⟩
  have hpre : q ⁻¹' U₀ ⊆ T := by
    change SeparationQuotient.mk ⁻¹' (SeparationQuotient.mk '' V) ⊆ T
    rw [SeparationQuotient.preimage_image_mk_open hVo]
    exact hVT
  have hthick : U₀ ⊆ q '' T := Set.image_mono hVT
  have hqn : q '' T ∈ 𝓝 (1 : Q) := by
    change SeparationQuotient.mk '' T ∈ 𝓝 (SeparationQuotient.mk (1 : H))
    exact SeparationQuotient.isOpenMap_mk.image_mem_nhds hTn
  let M : LocallyCompactGroupModel H T :=
    ⟨Q,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
      q,SeparationQuotient.surjective_mk,hT.image SeparationQuotient.continuous_mk,hqn,
      ⟨U₀,hUo.mem_nhds hU1,hpre⟩⟩
  refine ⟨{ toLocallyCompactGroupModel := M
            neighbourhood := U₀
            open_neighbourhood := hUo
            one_mem_neighbourhood := hU1
            small_neighbourhood := hpre
            thick_neighbourhood := hthick
            internal_sandwich := ?_ }⟩
  intro F U hF hU hFU hUU
  have hFc : IsCompact (q ⁻¹' F) :=
    SeparationQuotient.isInducing_mk.isCompact_preimage' hF (by
      rw [SeparationQuotient.range_mk]
      exact Set.subset_univ _)
  have hUo' : IsOpen (q ⁻¹' U) := hU.preimage SeparationQuotient.continuous_mk
  exact internal_finite_sandwich_of_basis u G H R hbasis hR (q ⁻¹' F) (q ⁻¹' U) hFc hUo'
    (Set.preimage_mono hFU)

end DirectedCycles
