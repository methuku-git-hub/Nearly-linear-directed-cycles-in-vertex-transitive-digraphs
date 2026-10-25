module

public import DirectedCycles.ShrinkingGroupNeighbourhoods
public import DirectedCycles.CompactnessFromInternalCovers

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Pointwise Topology
namespace DirectedCycles
namespace ShrinkingGroupNeighbourhoods
variable {G : Type*} [Group G] (S : ShrinkingGroupNeighbourhoods G)

theorem subgroup_nhds_basis (H : Subgroup G) (hH : H ≤ S.conjugationSubgroup) (x : H) :
    (@nhds H (S.subgroupFilterBasis H hH).topology x).HasBasis (fun _ : ℕ => True)
      (fun n => (fun y : H => x*y) '' (H.subtype ⁻¹' S.sets n)) := by
  apply ((S.subgroupFilterBasis H hH).nhds_hasBasis x).to_hasBasis
  · rintro U ⟨n,rfl⟩
    exact ⟨n,trivial,Set.Subset.rfl⟩
  · intro n hn
    exact ⟨H.subtype ⁻¹' S.sets n,⟨n,rfl⟩,Set.Subset.rfl⟩

theorem subgroup_compact_of_covers (H : Subgroup G) (hH : H ≤ S.conjugationSubgroup) (T : Set H)
    (hcover : ∀ n, ∃ F : Finset H, T ⊆ ⋃ x ∈ F,
      (fun y : H => x*y) '' (H.subtype ⁻¹' S.sets n))
    (hsat : ∀ c : ℕ → H,
      (∀ N, ∃ z ∈ T, ∀ n ≤ N, z ∈ (fun y : H => c n*y) '' (H.subtype ⁻¹' S.sets n)) →
      ∃ z ∈ T, ∀ n, z ∈ (fun y : H => c n*y) '' (H.subtype ⁻¹' S.sets n)) :
    @IsCompact H (S.subgroupFilterBasis H hH).topology T := by
  let : TopologicalSpace H := (S.subgroupFilterBasis H hH).topology
  apply compact_of_finite_covers_and_saturation T (fun n => H.subtype ⁻¹' S.sets n)
    (S.subgroup_nhds_basis H hH) ?_ ?_ hcover hsat
  · intro n
    ext x
    change (x⁻¹).val ∈ S.sets n ↔ x.val ∈ S.sets n
    change (x.val)⁻¹ ∈ S.sets n ↔ x.val ∈ S.sets n
    rw [← Set.mem_inv,S.inv_eq]
  · intro n g hg
    rw [pow_two] at hg
    obtain ⟨a,ha,b,hb,rfl⟩ := hg
    apply S.sq_subset n
    rw [pow_two]
    exact Set.mul_mem_mul ha hb

end ShrinkingGroupNeighbourhoods

/-- Restriction of an actual finite translate cover to a subgroup. -/
theorem finite_translate_cover_subgroup {G : Type*} [Group G]
    (H : Subgroup G) (T B : Set G) (hB : B ⊆ H) (F : Finset G)
    (hF : (F : Set G) ⊆ H) (hcover : T ⊆ (F : Set G)*B) :
    ∃ E : Finset H, H.subtype ⁻¹' T ⊆ ⋃ x ∈ E,
      (fun y : H => x*y) '' (H.subtype ⁻¹' B) := by
  classical
  let lift : F → H := fun x => ⟨x.val,hF x.property⟩
  let E := Finset.univ.image lift
  refine ⟨E,?_⟩
  intro z hz
  obtain ⟨f,hf,b,hb,he⟩ := hcover hz
  let fH : H := ⟨f,hF hf⟩
  let bH : H := ⟨b,hB hb⟩
  apply Set.mem_iUnion.mpr ⟨fH,?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨?_,bH,hb,Subtype.ext he⟩
  exact Finset.mem_image.mpr ⟨⟨f,hf⟩,Finset.mem_univ _,rfl⟩

end DirectedCycles
