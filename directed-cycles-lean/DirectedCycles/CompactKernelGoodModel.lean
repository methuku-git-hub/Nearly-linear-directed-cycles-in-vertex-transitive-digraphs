import DirectedCycles.InternalGoodModel
import DirectedCycles.CompactKernelQuotient

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
universe u
variable {G : Type u} [Group G] {T : Set G} {Internal : Set G → Prop}

/-- Quotienting a good model by an actual compact normal subgroup inside
its small neighbourhood preserves all good-model properties. Compact
preimages in the quotient justify the full internal sandwich. -/
noncomputable def compactKernelGoodModel
    (M : InternalLocallyCompactGroupModel G T Internal)
    (N : Subgroup M.carrier) [N.Normal] (hN : IsCompact (N : Set M.carrier))
    (hNU : (N : Set M.carrier) ⊆ M.neighbourhood) :
    InternalLocallyCompactGroupModel G T Internal := by
  let : IsClosed (N : Set M.carrier) := hN.isClosed
  let q := QuotientGroup.mk' N
  let : TopologicalSpace.MetrizableSpace (M.carrier ⧸ N) :=
    group_metrizable_of_countable_nhds
  have hproper := compact_kernel_quotient_proper N hN
  let hv := compact_kernel_quotient_small_preimage N hN
    M.neighbourhood M.open_neighbourhood hNU
  let V := Classical.choose hv
  have hV := (Classical.choose_spec hv).1
  have hV1 := (Classical.choose_spec hv).2.1
  have hVO := (Classical.choose_spec hv).2.2
  let f := q.comp M.map
  have hf : Function.Surjective f := QuotientGroup.mk_surjective.comp M.surjective
  have himage : f '' T = q '' (M.map '' T) := Set.image_comp q M.map T
  have hsmall : f ⁻¹' V ⊆ T := by
    intro x hx
    exact M.small_neighbourhood (hVO hx)
  have hthick : V ⊆ f '' T := by
    intro y hy
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨x,hsmall hy,rfl⟩
  have hcompact : IsCompact (f '' T) := by
    rw [himage]
    exact M.compact_image.image QuotientGroup.continuous_mk
  have hnhds : f '' T ∈ 𝓝 (1 : M.carrier ⧸ N) :=
    Filter.mem_of_superset (hV.mem_nhds hV1) hthick
  let M' : LocallyCompactGroupModel G T :=
    ⟨M.carrier ⧸ N,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
      inferInstance,f,hf,hcompact,hnhds,⟨V,hV.mem_nhds hV1,hsmall⟩⟩
  refine { toLocallyCompactGroupModel := M'
           neighbourhood := V
           open_neighbourhood := hV
           one_mem_neighbourhood := hV1
           small_neighbourhood := hsmall
           thick_neighbourhood := hthick
           internal_sandwich := ?_ }
  intro F O hF hO hFO hOV
  obtain ⟨B,hB,hFB,hBO⟩ := M.internal_sandwich (q ⁻¹' F) (q ⁻¹' O)
    (hproper.isCompact_preimage hF) (hO.preimage QuotientGroup.continuous_mk)
    (Set.preimage_mono hFO) ((Set.preimage_mono hOV).trans hVO)
  exact ⟨B,hB,hFB,hBO⟩

theorem compactKernelGoodModel_map
    (M : InternalLocallyCompactGroupModel G T Internal)
    (N : Subgroup M.carrier) [N.Normal] (hN : IsCompact (N : Set M.carrier))
    (hNU : (N : Set M.carrier) ⊆ M.neighbourhood) (x : G) :
    (compactKernelGoodModel M N hN hNU).map x = QuotientGroup.mk' N (M.map x) := rfl
end DirectedCycles
