import DirectedCycles.InternalSetLogic
import DirectedCycles.InternalTranslateSaturation

set_option autoImplicit false
open Filter
namespace DirectedCycles

theorem ultraSet_empty {ι : Type*} (f : Filter ι) [f.NeBot]
    (G : ι → Type*) [∀ i, Group (G i)] :
    ultraSet f G (fun _ => ∅) = ∅ := by
  ext z
  obtain ⟨x,rfl⟩ := ultraMk_surjective f G z
  simp only [ultraMk_mem_ultraSet_iff,Set.mem_empty_iff_false]
  constructor
  · intro h
    obtain ⟨i,hi⟩ := h.exists
    exact hi
  · intro h
    exact h.elim

theorem ultraSet_union {ι : Type*} (u : Ultrafilter ι)
    (G : ι → Type*) [∀ i, Group (G i)] (A B : ∀ i, Set (G i)) :
    ultraSet (u : Filter ι) G (fun i => A i ∪ B i) =
      ultraSet (u : Filter ι) G A ∪ ultraSet (u : Filter ι) G B := by
  ext z
  obtain ⟨x,rfl⟩ := ultraMk_surjective (u : Filter ι) G z
  simp only [Set.mem_union,ultraMk_mem_ultraSet_iff,Ultrafilter.eventually_or]

/-- Internal finite sets restricted to a subgroup. -/
def IsInternalFiniteIn {ι : Type*} (u : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (H : Subgroup (GroupUltraproduct (u : Filter ι) G)) (T : Set H) : Prop :=
  ∃ B : ∀ i, Finset (G i), T = H.subtype ⁻¹' ultraSet (u : Filter ι) G (fun i => (B i : Set (G i)))

theorem IsInternalFiniteIn.empty {ι : Type*} (u : Ultrafilter ι)
    (G : ι → Type*) [∀ i, Group (G i)] (H : Subgroup (GroupUltraproduct (u : Filter ι) G)) :
    IsInternalFiniteIn u G H ∅ := by
  refine ⟨fun _ => ∅,?_⟩
  simp [ultraSet_empty]

theorem IsInternalFiniteIn.union {ι : Type*} {u : Ultrafilter ι}
    {G : ι → Type*} [∀ i, Group (G i)] {H : Subgroup (GroupUltraproduct (u : Filter ι) G)}
    {S T : Set H} (hS : IsInternalFiniteIn u G H S) (hT : IsInternalFiniteIn u G H T) :
    IsInternalFiniteIn u G H (S ∪ T) := by
  classical
  obtain ⟨A,rfl⟩ := hS
  obtain ⟨B,rfl⟩ := hT
  refine ⟨fun i => A i ∪ B i,?_⟩
  simp only [Finset.coe_union,ultraSet_union,Set.preimage_union]

theorem IsInternalFiniteIn.biUnion_finset {ι J : Type*} {u : Ultrafilter ι}
    {G : ι → Type*} [∀ i, Group (G i)] {H : Subgroup (GroupUltraproduct (u : Filter ι) G)}
    (F : Finset J) (B : J → Set H) (hB : ∀ j ∈ F, IsInternalFiniteIn u G H (B j)) :
    IsInternalFiniteIn u G H (⋃ j ∈ F, B j) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using IsInternalFiniteIn.empty u G H
  | @insert j F hj ih =>
    simp only [Finset.set_biUnion_insert]
    exact (hB j (Finset.mem_insert_self _ _)).union
      (ih (fun k hk => hB k (Finset.mem_insert_of_mem hk)))

theorem subgroup_preimage_leftTranslate {V : Type*} [Group V]
    (H : Subgroup V) (c : H) (B : Set V) :
    H.subtype ⁻¹' ((fun x => c.val*x) '' B) =
      (fun x : H => c*x) '' (H.subtype ⁻¹' B) := by
  ext z
  constructor
  · rintro ⟨b,hb,he⟩
    change c.val*b=z.val at he
    have hbH : b ∈ H := by
      have hb' : b = c.val⁻¹*z.val := by rw [← he]; simp
      rw [hb']
      exact H.mul_mem (H.inv_mem c.property) z.property
    exact ⟨⟨b,hbH⟩,hb,Subtype.ext he⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨b.val,hb,rfl⟩

theorem IsInternalFiniteIn.leftTranslate {ι : Type*} {u : Ultrafilter ι}
    {G : ι → Type*} [∀ i, Group (G i)] {H : Subgroup (GroupUltraproduct (u : Filter ι) G)}
    {T : Set H} (hT : IsInternalFiniteIn u G H T) (c : H) :
    IsInternalFiniteIn u G H ((fun x : H => c*x) '' T) := by
  classical
  obtain ⟨A,rfl⟩ := hT
  obtain ⟨a,ha⟩ := ultraMk_surjective (u : Filter ι) G c.val
  refine ⟨fun i => (A i).image (fun x => a i*x),?_⟩
  simp only [Finset.coe_image,ultraSet_leftTranslate,ha,subgroup_preimage_leftTranslate]

end DirectedCycles
