module

public import DirectedCycles.LocalWordPowerMaps

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*}

/-- BGT's finite local approximate group, including the 200-letter domain
condition and the symmetric covering set inside the third word power. -/
structure IsLocalFiniteApproximateGroup (L : LocalGroupAlgebra G) (K : ℕ) (A : Finset G) : Prop where
  one_le : 1 ≤ K
  one_mem : L.one ∈ A
  inv_mem : ∀ a ∈ A, L.inv a ∈ A
  allProducts : L.AllProductsDefined (A : Set G) 200
  cover : ∃ X : Finset G, X.card ≤ K ∧ (∀ x ∈ X, L.inv x ∈ X) ∧
    (X : Set G) ⊆ L.wordPower (A : Set G) 3 ∧
    L.wordPower (A : Set G) 2 ⊆ L.setMul (X : Set G) (A : Set G)

namespace IsLocalFiniteApproximateGroup
variable {H : Type*} [DecidableEq H] {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}
    {K : ℕ} {A : Finset G}

/-- An actual local homomorphism sends a finite local K-approximate group to
a finite local K-approximate group. Product domains and the covering witnesses
are transported explicitly. -/
theorem image (hA : IsLocalFiniteApproximateGroup L K A) (f : LocalGroupHom L M) :
    IsLocalFiniteApproximateGroup M K (A.image f.toFun) := by
  classical
  have hcoe : (↑(A.image f.toFun) : Set H) = f.toFun '' (A : Set G) := Finset.coe_image
  refine ⟨hA.one_le,?_,?_,?_,?_⟩
  · exact Finset.mem_image.mpr ⟨L.one,hA.one_mem,f.map_one⟩
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨L.inv a,hA.inv_mem a ha,f.map_inv a⟩
  · rw [hcoe]
    exact hA.allProducts.image f
  · obtain ⟨X,hXcard,hXi,hX3,hcover⟩ := hA.cover
    refine ⟨X.image f.toFun,(Finset.card_image_le).trans hXcard,?_,?_,?_⟩
    · intro x hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨L.inv a,hXi a ha,f.map_inv a⟩
    · intro x hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      rw [hcoe]
      exact LocalGroupAlgebra.wordPower_image_subset f (A : Set G) 3 ⟨a,hX3 ha,rfl⟩
    · rw [hcoe,← LocalGroupAlgebra.wordPower_image f hA.allProducts (by omega : 2 ≤ 200)]
      rintro x ⟨z,hz,rfl⟩
      obtain ⟨a,ha,b,hb,hm⟩ := hcover hz
      exact ⟨f.toFun a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,
        f.toFun b,⟨b,hb,rfl⟩,f.map_mul hm⟩
end IsLocalFiniteApproximateGroup
end DirectedCycles
