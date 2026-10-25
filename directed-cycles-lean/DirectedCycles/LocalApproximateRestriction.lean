module

public import DirectedCycles.LocalApproximateGroups
public import DirectedCycles.LocalProductRestriction

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace IsLocalFiniteApproximateGroup
variable {G : Type*} {L : LocalGroupAlgebra G} {K : ℕ} {A : Finset G}
    (S : Set G) [DecidablePred (· ∈ S)] (h1 : L.one ∈ S)
    (hi : ∀ x ∈ S, L.inv x ∈ S)

/-- A restriction containing every required word value preserves the exact
covering constant, including the symmetric third-power covering set. -/
theorem restrict (hA : IsLocalFiniteApproximateGroup L K A)
    (hS : ∀ n ≤ 200, L.wordPower (A : Set G) n ⊆ S) :
    IsLocalFiniteApproximateGroup (L.restrict S h1 hi) K (A.subtype (· ∈ S)) := by
  classical
  let M := L.restrict S h1 hi
  let f := LocalGroupHom.inclusion L S h1 hi
  have hAS : (A : Set G) ⊆ S := by
    simpa only [L.wordPower_one] using hS 1 (by omega)
  have hcoe : (↑(A.subtype (· ∈ S)) : Set S) = Subtype.val ⁻¹' (A : Set G) := by
    ext x
    exact Finset.mem_subtype
  have hdom := L.allProductsDefined_restrict S h1 hi hA.allProducts hS
  refine ⟨hA.one_le,?_,?_,?_,?_⟩
  · exact Finset.mem_subtype.mpr hA.one_mem
  · intro x hx
    exact Finset.mem_subtype.mpr (hA.inv_mem x.val (Finset.mem_subtype.mp hx))
  · simpa only [hcoe] using hdom
  · obtain ⟨X,hXcard,hXi,hX3,hcover⟩ := hA.cover
    have hXS : (X : Set G) ⊆ S := hX3.trans (hS 3 (by omega))
    refine ⟨X.subtype (· ∈ S),?_,?_,?_,?_⟩
    · rw [Finset.card_subtype]
      exact (Finset.card_filter_le X (· ∈ S)).trans hXcard
    · intro x hx
      exact Finset.mem_subtype.mpr (hXi x.val (Finset.mem_subtype.mp hx))
    · intro x hx
      have hx3 : x.val ∈ L.wordPower (A : Set G) 3 := hX3 (Finset.mem_subtype.mp hx)
      rw [← L.wordPower_restrict_image S h1 hi hA.allProducts hS hAS (by omega : 3 ≤ 200)] at hx3
      obtain ⟨y,hy,he⟩ := hx3
      have hey : y = x := Subtype.ext he
      simpa only [hcoe,hey] using hy
    · intro z hz
      have hz' : z.val ∈ L.wordPower (A : Set G) 2 := by
        have hh := LocalGroupAlgebra.wordPower_image_subset f
          (↑(A.subtype (· ∈ S)) : Set S) 2 ⟨z,hz,rfl⟩
        obtain ⟨l,hlen,hl,hp⟩ := hh
        refine ⟨l,hlen,?_,hp⟩
        intro x hx
        obtain ⟨y,hy,he⟩ := hl x hx
        exact he ▸ Finset.mem_subtype.mp hy
      obtain ⟨x,hx,a,ha,hm⟩ := hcover hz'
      exact ⟨⟨x,hXS hx⟩,Finset.mem_subtype.mpr hx,
        ⟨a,hAS ha⟩,Finset.mem_subtype.mpr ha,hm⟩
end IsLocalFiniteApproximateGroup
end DirectedCycles
