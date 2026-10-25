module

public import DirectedCycles.LocalFiniteProductCard
public import DirectedCycles.LocalSubgroupTransport
public import DirectedCycles.LocalWordPowerMonotonicity
public import DirectedCycles.LocalTwoProducts

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Fintype G] {L : LocalGroupAlgebra G} {A : Finset G}

/-- A finite local 1-approximate group is an actual global subgroup. Totality
comes from its domain condition; equality A squared = A comes from doubling
and inclusion, so no global ambient multiplication is assumed. -/
theorem local_one_approximate_isGlobalSubgroup
    (hA : IsLocalFiniteApproximateGroup L 1 A) : L.IsGlobalSubgroup (A : Set G) := by
  classical
  let B := (L.wordPower (A : Set G) 2).toFinset
  have hAB : A ⊆ B := by
    intro x hx
    apply Set.mem_toFinset.mpr
    have hh := L.wordPower_subset_wordPower hA.one_mem hA.allProducts
      (by omega : 1 ≤ 2) (by omega : 2 ≤ 200)
    apply hh
    rw [L.wordPower_one]
    exact hx
  have hcard : B.card ≤ A.card := by
    have hc : B.card = Nat.card (L.wordPower (A : Set G) 2) := by
      rw [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card']
    rw [hc]
    simpa only [one_mul] using local_approximate_doubling hA
  have he : A = B := Finset.eq_of_subset_of_card_le hAB hcard
  refine ⟨hA.one_mem,hA.inv_mem,?_⟩
  intro x hx y hy
  have hxy : ∀ v ∈ [x,y], v ∈ (A : Set G) := by
    intro v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl
    · exact hx
    · exact hy
  obtain ⟨z,hz⟩ := hA.allProducts [x,y] (by simp only [List.length_cons,List.length_nil]; omega) hxy
  have hzB : z ∈ B := Set.mem_toFinset.mpr ⟨[x,y],rfl,hxy,hz⟩
  have hzA : z ∈ A := by rw [he]; exact hzB
  exact ⟨z,hzA,(LocalGroupAlgebra.Product.pair_iff L _ _ _).1 hz⟩

namespace LocalGroupAlgebra
variable {H : Set G}

omit [Fintype G] in
theorem IsGlobalSubgroup.escapeNorm_mul_le (hH : L.IsGlobalSubgroup H)
    {a b c : G} (hm : L.mulRel a b c) :
    L.escapeNorm H c ≤ L.escapeNorm H a+L.escapeNorm H b := by
  by_cases ha : a ∈ H
  · by_cases hb : b ∈ H
    · obtain ⟨v,hv,hvrel⟩ := hH.mul_total a ha b hb
      have hc : c ∈ H := (L.unique hm hvrel).symm ▸ hv
      rw [hH.escapeNorm_eq_zero (Set.Subset.refl _) hH.one_mem hc]
      exact add_nonneg (L.escapeNorm_nonneg hH.one_mem a) (L.escapeNorm_nonneg hH.one_mem b)
    · rw [L.escapeNorm_eq_one_of_not_mem hH.one_mem hb]
      exact (L.escapeNorm_le_one hH.one_mem c).trans (le_add_of_nonneg_left (L.escapeNorm_nonneg hH.one_mem a))
  · rw [L.escapeNorm_eq_one_of_not_mem hH.one_mem ha]
    exact (L.escapeNorm_le_one hH.one_mem c).trans (le_add_of_nonneg_right (L.escapeNorm_nonneg hH.one_mem b))

omit [Fintype G] in
theorem IsGlobalSubgroup.escapeNorm_product_le (hH : L.IsGlobalSubgroup H)
    {l : List G} {x : G} (hp : L.Product l x) :
    L.escapeNorm H x ≤ (l.map (L.escapeNorm H)).sum := by
  induction l generalizing x with
  | nil =>
    have he := (Product.nil_iff L).1 hp
    subst x
    simp only [L.escapeNorm_one hH.one_mem,List.map_nil,List.sum_nil,le_refl]
  | cons a l ih =>
    obtain ⟨u,v,hu,hv,hm⟩ := hp.split_allow_empty L (a := [a]) (b := l) rfl
    have he := (Product.singleton_iff L).1 hu
    subst u
    simpa only [List.map_cons,List.sum_cons] using
      (hH.escapeNorm_mul_le hm).trans (add_le_add le_rfl (ih hv))
end LocalGroupAlgebra
end DirectedCycles
