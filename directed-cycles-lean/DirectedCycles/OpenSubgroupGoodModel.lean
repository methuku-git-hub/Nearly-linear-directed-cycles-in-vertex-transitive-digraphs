module

public import DirectedCycles.InternalGoodModel
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Metrizable.Basic

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
universe u
variable {G H : Type u} [Group G] [Group H]

/-- Restriction of a model homomorphism to the full preimage of an actual
target subgroup. -/
def subgroupModelHom (π : G →* H) (S : Subgroup H) : S.comap π →* S where
  toFun x := ⟨π x.val,x.property⟩
  map_one' := Subtype.ext (map_one π)
  map_mul' x y := Subtype.ext (map_mul π x.val y.val)

theorem subgroupModelHom_surjective (π : G →* H) (S : Subgroup H)
    (hπ : Function.Surjective π) : Function.Surjective (subgroupModelHom π S) := by
  intro y
  obtain ⟨x,hx⟩ := hπ y.val
  exact ⟨⟨x,show π x ∈ S from hx.symm ▸ y.property⟩,Subtype.ext hx⟩

theorem subgroupModelHom_image (π : G →* H) (S : Subgroup H) (T : Set G) :
    subgroupModelHom π S '' ((S.comap π).subtype ⁻¹' T) =
      S.subtype ⁻¹' (π '' T) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.val,hx,rfl⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨⟨x,show π x ∈ S from he.symm ▸ y.property⟩,hx,Subtype.ext he⟩

/-- The literal predicate obtained by restricting internal sets to a
subgroup. This does not assert that an arbitrary subgroup is internal. -/
def RestrictedInternal (S : Subgroup G) (Internal : Set G → Prop) (D : Set S) : Prop :=
  ∃ B : Set G, Internal B ∧ S.subtype ⁻¹' B = D

variable {T : Set G} {Internal : Set G → Prop}

/-- Restricting a good model to an open target subgroup preserves its
actual compact image and internal approximation property. -/
noncomputable def openSubgroupGoodModel
    (M : InternalLocallyCompactGroupModel G T Internal)
    (S : Subgroup M.carrier) (hS : IsOpen (S : Set M.carrier)) :
    InternalLocallyCompactGroupModel (S.comap M.map) ((S.comap M.map).subtype ⁻¹' T)
      (RestrictedInternal (S.comap M.map) Internal) := by
  let : LocallyCompactSpace S := hS.locallyCompactSpace
  let : TopologicalSpace.MetrizableSpace M.carrier := M.metrizable
  let : TopologicalSpace.MetrizableSpace S := Topology.IsEmbedding.subtypeVal.metrizableSpace
  let f := subgroupModelHom M.map S
  let T' := (S.comap M.map).subtype ⁻¹' T
  let V := S.subtype ⁻¹' M.neighbourhood
  have hVo : IsOpen V := M.open_neighbourhood.preimage continuous_subtype_val
  have hV1 : (1 : S) ∈ V := M.one_mem_neighbourhood
  have hsmall : f ⁻¹' V ⊆ T' := fun _ hx => M.small_neighbourhood hx
  have hf := subgroupModelHom_surjective M.map S M.surjective
  have hthick : V ⊆ f '' T' := by
    intro y hy
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨x,hsmall hy,rfl⟩
  have hcompact : IsCompact (f '' T') := by
    rw [subgroupModelHom_image]
    exact (S.isClosed_of_isOpen hS).isClosedEmbedding_subtypeVal.isCompact_preimage M.compact_image
  have hnhds : f '' T' ∈ 𝓝 (1 : S) := Filter.mem_of_superset (hVo.mem_nhds hV1) hthick
  let M' : LocallyCompactGroupModel (S.comap M.map) T' :=
    ⟨S,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
      f,hf,hcompact,hnhds,⟨V,hVo.mem_nhds hV1,hsmall⟩⟩
  refine { toLocallyCompactGroupModel := M'
           neighbourhood := V
           open_neighbourhood := hVo
           one_mem_neighbourhood := hV1
           small_neighbourhood := hsmall
           thick_neighbourhood := hthick
           internal_sandwich := ?_ }
  intro F O hF hO hFO hOV
  have hOU : S.subtype '' O ⊆ M.neighbourhood := by
    rintro x ⟨y,hy,rfl⟩
    exact hOV hy
  obtain ⟨B,hB,hFB,hBO⟩ := M.internal_sandwich (S.subtype '' F) (S.subtype '' O)
    (hF.image continuous_subtype_val) (hS.isOpenMap_subtype_val _ hO)
    (Set.image_mono hFO) hOU
  refine ⟨(S.comap M.map).subtype ⁻¹' B,⟨B,hB,rfl⟩,?_,?_⟩
  · intro x hx
    apply hFB
    exact ⟨f x,hx,rfl⟩
  · intro x hx
    obtain ⟨y,hy,he⟩ := hBO hx
    have hye : y = f x := Subtype.ext he
    change f x ∈ O
    rw [← hye]
    exact hy

theorem openSubgroupGoodModel_map
    (M : InternalLocallyCompactGroupModel G T Internal)
    (S : Subgroup M.carrier) (hS : IsOpen (S : Set M.carrier)) (x : S.comap M.map) :
    ((openSubgroupGoodModel M S hS).map x).val = M.map x.val := rfl
end DirectedCycles
