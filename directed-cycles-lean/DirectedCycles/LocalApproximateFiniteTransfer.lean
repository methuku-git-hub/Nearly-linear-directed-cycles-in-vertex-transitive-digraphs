module

public import DirectedCycles.LocalApproximateUltra

@[expose] public section

set_option autoImplicit false
open Filter
namespace DirectedCycles
variable {ι : Type*} (u : Ultrafilter ι) (G : ι → Type*)
    (L : ∀ i, LocalGroupAlgebra (G i))

theorem localUltra_inv_closed_iff (A : ∀ i, Set (G i)) :
    (∀ x ∈ localUltraSet (u : Filter ι) G A,
      (localUltraAlgebra (u : Filter ι) G L).inv x ∈ localUltraSet (u : Filter ι) G A) ↔
    ∀ᶠ i in (u : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i := by
  change (localUltraSet (u : Filter ι) G A ⊆
    localUltraMap (u : Filter ι) G G (fun i => (L i).inv) ⁻¹' localUltraSet (u : Filter ι) G A) ↔ _
  rw [localUltraMap_preimage,localUltraSet_subset_iff_eventually u G (fun i => (L i).one)]
  rfl

/-- A finite covering witness in the actual local ultraproduct supplies
finite component witnesses, with the same covering constant, on a large set
of indices. No first-order transfer axiom is used. -/
theorem localApproximateSet_eventually {K : ℕ} (A : ∀ i, Set (G i))
    (hA : IsLocalApproximateSet (localUltraAlgebra (u : Filter ι) G L) K
      (localUltraSet (u : Filter ι) G A)) :
    ∀ᶠ i in (u : Filter ι), IsLocalApproximateSet (L i) K (A i) := by
  classical
  let F : Filter ι := u
  obtain ⟨X,hXcard,hXi,hX3,hcover⟩ := hA.cover
  have hreps : ∀ x : X, ∃ a : ∀ i, G i, localUltraMk F G a = x.val := by
    intro x
    exact Quotient.mk_surjective x.val
  choose r hr using hreps
  let Xi : ∀ i, Finset (G i) := fun i => Finset.univ.image (fun x : X => r x i)
  have hXiEq : localUltraSet F G (fun i => (Xi i : Set (G i))) = (X : Set _) := by
    simp only [Xi,Finset.coe_image,Finset.coe_univ,Set.image_univ]
    rw [localUltraSet_finite_range]
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      change localUltraMk F G (r y) ∈ (X : Set _)
      rw [hr y]
      exact y.property
    · intro hx
      exact ⟨⟨x,hx⟩,hr ⟨x,hx⟩⟩
  have hcard : ∀ i, (Xi i).card ≤ K := by
    intro i
    exact Finset.card_image_le.trans (by simpa only [Finset.card_univ,Fintype.card_coe] using hXcard)
  have hone : ∀ᶠ i in F, (L i).one ∈ A i := (localUltraMk_mem_iff F G A _).1 hA.one_mem
  have hinv := (localUltra_inv_closed_iff u G L A).1 hA.inv_mem
  have hdom := (localUltra_allProductsDefined_iff u G L A 200).1 hA.allProducts
  have hXinv : ∀ᶠ i in F, ∀ x ∈ Xi i, (L i).inv x ∈ Xi i := by
    apply (localUltra_inv_closed_iff u G L (fun i => (Xi i : Set (G i)))).1
    change ∀ x ∈ localUltraSet F G (fun i => (Xi i : Set (G i))),
      (localUltraAlgebra F G L).inv x ∈ localUltraSet F G (fun i => (Xi i : Set (G i)))
    rw [hXiEq]
    exact hXi
  have hXpower : ∀ᶠ i in F, (Xi i : Set (G i)) ⊆ (L i).wordPower (A i) 3 := by
    apply (localUltraSet_subset_iff_eventually u G (fun i => (L i).one) _ _).1
    rw [hXiEq,← localUltra_wordPower u G L A 3]
    exact hX3
  have hcov : ∀ᶠ i in F, (L i).wordPower (A i) 2 ⊆ (L i).setMul (Xi i : Set (G i)) (A i) := by
    apply (localUltraSet_subset_iff_eventually u G (fun i => (L i).one) _ _).1
    rw [← localUltra_wordPower u G L A 2,localUltraSet_mul F G L,hXiEq]
    exact hcover
  filter_upwards [hone,hinv,hdom,hXinv,hXpower,hcov] with i h1 hi hd hxi hx3 hc
  exact ⟨hA.one_le,h1,hi,hd,⟨Xi i,hcard i,hxi,hx3,hc⟩⟩

/-- The finite form used after descending a quotient construction. -/
theorem localFiniteApproximate_eventually {K : ℕ} (A : ∀ i, Finset (G i))
    (hA : IsLocalApproximateSet (localUltraAlgebra (u : Filter ι) G L) K
      (localUltraSet (u : Filter ι) G (fun i => (A i : Set (G i))))) :
    ∀ᶠ i in (u : Filter ι), IsLocalFiniteApproximateGroup (L i) K (A i) :=
  (localApproximateSet_eventually u G L _ hA).mono
    (fun _ hi => localApproximateSet_finset_iff.mp hi)
end DirectedCycles
