module

public import DirectedCycles.InternalSubgroupTransfer
public import DirectedCycles.UltraproductInternalSets

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Pointwise
namespace DirectedCycles

/-- A genuine finite cover in the ultraproduct yields component covers with
one uniform cardinal bound. -/
theorem finite_cover_components {ι : Type*} (u : Ultrafilter ι)
    (G : ι → Type*) [∀ i, Group (G i)] (A B : ∀ i, Set (G i))
    (F : Finset (GroupUltraproduct (u : Filter ι) G))
    (hcover : ultraSet (u : Filter ι) G A ⊆ (F : Set _)*ultraSet (u : Filter ι) G B) :
    ∃ E : ∀ i, Finset (G i), (∀ i, (E i).card ≤ F.card) ∧
      ∀ᶠ i in (u : Filter ι), A i ⊆ (E i : Set (G i))*B i := by
  classical
  have hex : ∀ x : F, ∃ a : ∀ i, G i, ultraMk (u : Filter ι) G a = x.val :=
    fun x => ultraMk_surjective _ G x.val
  choose a ha using hex
  let E : ∀ i, Finset (G i) := fun i => Finset.univ.image (fun x : F => a x i)
  have he : ultraSet (u : Filter ι) G (fun i => (E i : Set (G i))) = (F : Set _) := by
    simp only [E,Finset.coe_image,Finset.coe_univ,Set.image_univ,ultraSet_finite_range]
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      change ultraMk (u : Filter ι) G (a y) ∈ (F : Set _)
      rw [ha y]
      exact y.property
    · exact fun hx => ⟨⟨x,hx⟩,ha ⟨x,hx⟩⟩
  refine ⟨E,fun i => Finset.card_image_le.trans (by simp),?_⟩
  apply (ultraSet_subset_iff_eventually u G _ _).1
  rw [ultraSet_mul,he]
  exact hcover
end DirectedCycles
