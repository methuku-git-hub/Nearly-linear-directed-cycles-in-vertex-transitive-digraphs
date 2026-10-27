module

public import DirectedCycles.LocalApproximateFiniteTransfer
public import DirectedCycles.LocalFiniteProductCard
public import Mathlib.Data.Set.Card

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- Actual finite local covers of internal sets transfer to finite component
covers with a uniform bound on the number of translating elements. -/
theorem local_finite_cover_components (A B : ∀ i, Finset (G i))
    (X : Finset (LocalUltraproduct (U : Filter ι) G))
    (hcover : localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) ⊆
      (localUltraAlgebra (U : Filter ι) G L).setMul (X : Set _)
        (localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))))) :
    ∃ Y : ∀ i, Finset (G i), (∀ i, (Y i).card ≤ X.card) ∧
      ∀ᶠ i in (U : Filter ι), (A i : Set (G i)) ⊆ (L i).setMul (Y i : Set (G i)) (B i : Set (G i)) := by
  classical
  have hreps : ∀ x : X, ∃ a : ∀ i, G i, localUltraMk (U : Filter ι) G a = x.val := by
    intro x
    exact Quotient.mk_surjective x.val
  choose r hr using hreps
  let Y : ∀ i, Finset (G i) := fun i => Finset.univ.image (fun x : X => r x i)
  have hY : localUltraSet (U : Filter ι) G (fun i => (Y i : Set (G i))) = (X : Set _) := by
    simp only [Y,Finset.coe_image,Finset.coe_univ,Set.image_univ]
    rw [localUltraSet_finite_range]
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      change localUltraMk (U : Filter ι) G (r y) ∈ (X : Set _)
      rw [hr y]
      exact y.property
    · intro hx
      exact ⟨⟨x,hx⟩,hr ⟨x,hx⟩⟩
  refine ⟨Y,?_,?_⟩
  · intro i
    exact Finset.card_image_le.trans (by simp only [Finset.card_univ,Fintype.card_coe,le_refl])
  · apply (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) _ _).1
    rw [localUltraSet_mul,hY]
    exact hcover

/-- A finite local translate cover gives the genuine uniform component
cardinality ratio used by the large-subgroup reductions. -/
theorem local_density_of_internal_finite_cover [∀ i, Fintype (G i)]
    (A B : ∀ i, Finset (G i))
    (hcover : ∃ X : Finset (LocalUltraproduct (U : Filter ι) G),
      localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) ⊆
        (localUltraAlgebra (U : Filter ι) G L).setMul (X : Set _)
          (localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))))) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ᶠ i in (U : Filter ι), (A i).card ≤ J*(B i).card := by
  obtain ⟨X,hX⟩ := hcover
  obtain ⟨Y,hY,hcov⟩ := local_finite_cover_components U G L A B X hX
  refine ⟨X.card+1,by omega,?_⟩
  filter_upwards [hcov] with i hi
  have hsub := Nat.card_le_card_of_injective (Set.inclusion hi) (Set.inclusion_injective hi)
  have hmul := (L i).card_setMul_le (Y i) (B i)
  have hA : (A i).card ≤ (Y i).card*(B i).card := by
    simpa only [Nat.card_coe_set_eq,Set.ncard_coe_finset] using hsub.trans hmul
  exact hA.trans (Nat.mul_le_mul_right _ (by have := hY i; omega))
end DirectedCycles
