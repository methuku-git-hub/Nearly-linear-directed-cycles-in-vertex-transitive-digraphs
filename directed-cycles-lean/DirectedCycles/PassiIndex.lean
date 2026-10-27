module

public import DirectedCycles.PassiWords
public import DirectedCycles.AbelianQuotientBound
public import DirectedCycles.DenseBounds

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- The Passi-group index estimate with the source exponent, for any finite
r-generated group. Nilpotence is not needed for this implication. -/
theorem passi_index_of_multiplier {G : Type*} [Group G] [Finite G]
    (r D : ℕ) (hD : 0 < D) (hr : Group.rank G ≤ r)
    (H : AddSubgroup (passiGroup (G := G) D hD))
    (M : ℕ) (hM : 0 < M) (hexp : ∀ x, M • x ∈ H) :
    H.index ≤ M^(∑ j ∈ Finset.range (D-1), r^(j+1)) := by
  classical
  obtain ⟨S,hScard,hS⟩ := Group.rank_spec G
  let e := S.equivFinOfCardEq hScard
  let u : Fin (Group.rank G) → G := fun i => (e.symm i).val
  have hu : Subgroup.closure (Set.range u) = ⊤ := by
    have he : Set.range u = (S : Set G) := by
      ext x
      constructor
      · rintro ⟨i,rfl⟩
        exact (e.symm i).property
      · intro hx
        exact ⟨e ⟨x,hx⟩,congrArg Subtype.val (e.symm_apply_apply ⟨x,hx⟩)⟩
    rw [he,hS]
  have hi := additive_index_le_multiplier (passiWordGenerator D hD u)
    (passiWordGenerator_generates D hD u hu) H M hM hexp
  rw [positiveWordIndex_card] at hi
  refine hi.trans (Nat.pow_le_pow_right hM ?_)
  exact Finset.sum_le_sum (fun j _ => Nat.pow_le_pow_left hr _)

/-- Manuscript Theorem 5.4: a bounded integer multiplier for the actual
truncated group ring, its equivalent Passi formulation, and the stated index
bound. The explicit constants depend only on r, c and D. -/
theorem integer_generation_from_dense_set {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] (r c D : ℕ) (hD : 0 < D)
    (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c)
    (E : Finset G) (e₀ : G) (he₀ : e₀ ∈ E) :
    let R := ∑ i ∈ Finset.range c, r^(i+1)
    0 < denseMultiplierConstant R D ∧ 0 < denseMultiplierExponent R D ∧
    ∃ M : ℕ, 0 < M ∧
      (M : ℝ) ≤ denseMultiplierConstant R D *
        ((Nat.card G : ℝ)/E.card)^denseMultiplierExponent R D ∧
      (∀ x : TruncatedGroupRing G D,
        M • x ∈ AddSubgroup.closure (truncatedElement G D '' (E : Set G))) ∧
      (∀ x : passiGroup (G := G) D hD,
        M • x ∈ passiDifferences D hD (E : Set G) e₀) ∧
      (passiDifferences D hD (E : Set G) e₀).index ≤
        M^(∑ j ∈ Finset.range (D-1), r^(j+1)) := by
  refine ⟨denseMultiplierConstant_pos _ D,denseMultiplierExponent_pos _ D,?_⟩
  obtain ⟨M,hM,hbound,hspan⟩ := nilpotent_dense_generation r c D hr hc E ⟨e₀,he₀⟩
  have hpassi := passi_multiplier_of_augmentation D hD (E : Set G) e₀ M hspan
  exact ⟨M,hM,hbound,hspan,hpassi,passi_index_of_multiplier r D hD hr _ M hM hpassi⟩

end DirectedCycles
