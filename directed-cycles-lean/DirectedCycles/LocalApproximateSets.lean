module

public import DirectedCycles.LocalApproximateGroups

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A local approximate set need not itself be finite; its covering set is
finite. This is the form used for actual internal ultraproduct sets. -/
structure IsLocalApproximateSet {G : Type*} (L : LocalGroupAlgebra G) (K : ℕ) (A : Set G) : Prop where
  one_le : 1 ≤ K
  one_mem : L.one ∈ A
  inv_mem : ∀ a ∈ A, L.inv a ∈ A
  allProducts : L.AllProductsDefined A 200
  cover : ∃ X : Finset G, X.card ≤ K ∧ (∀ x ∈ X, L.inv x ∈ X) ∧
    (X : Set G) ⊆ L.wordPower A 3 ∧ L.wordPower A 2 ⊆ L.setMul (X : Set G) A

theorem localApproximateSet_finset_iff {G : Type*} {L : LocalGroupAlgebra G} {K : ℕ} {A : Finset G} :
    IsLocalApproximateSet L K (A : Set G) ↔ IsLocalFiniteApproximateGroup L K A := by
  constructor
  · intro h
    exact ⟨h.one_le,h.one_mem,h.inv_mem,h.allProducts,h.cover⟩
  · intro h
    exact ⟨h.one_le,h.one_mem,h.inv_mem,h.allProducts,h.cover⟩

namespace IsLocalApproximateSet
variable {G : Type*} {L : LocalGroupAlgebra G} {K : ℕ} {A : Set G}

theorem nonempty_cover (hA : IsLocalApproximateSet L K A) {X : Finset G}
    (hcover : L.wordPower A 2 ⊆ L.setMul (X : Set G) A) : X.Nonempty := by
  have hpow : L.one ∈ L.wordPower A 2 := by
    rw [L.wordPower_add hA.allProducts (m := 1) (n := 1) (by omega),L.wordPower_one]
    exact ⟨L.one,hA.one_mem,L.one,hA.one_mem,L.one_mul L.one⟩
  obtain ⟨x,hx,_,_,_⟩ := hcover hpow
  exact ⟨x,hx⟩
end IsLocalApproximateSet
end DirectedCycles
