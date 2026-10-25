module

public import DirectedCycles.ElementCocycleQuotient

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Ordered conjugation differences remain nilpotent after both quotients. -/
theorem elementFactorAction_nilpotent {G : Type*} [Group G] [Group.IsNilpotent G]
    (a : G) (c : ℕ) (hc : Group.nilpotencyClass G ≤ c)
    (xs : List (G ⧸ elementClosure a)) (hlen : c ≤ xs.length) :
    (xs.map (fun x => elementFactorAction a x-1)).prod = 0 := by
  obtain ⟨gs,rfl⟩ := List.map_surjective_iff.mpr (QuotientGroup.mk'_surjective (elementClosure a)) xs
  simp only [List.length_map] at hlen
  simp only [List.map_map,Function.comp_def,elementFactorAction_mk]
  apply LinearMap.ext
  intro x
  obtain ⟨v,rfl⟩ := (elementDifferenceRange a).mkQ_surjective x
  change (gs.map (fun g => quotientRepresentation _ _ (elementDifferenceRange_invariant a) g-1)).prod
    ((elementDifferenceRange a).mkQ v) = 0
  rw [quotientRepresentation_difference_product,
    normalAbelianAction_nilpotent (elementCommutators a) c hc gs hlen,
    LinearMap.zero_apply,map_zero]

/-- The cocycle's actual action satisfies the truncation nilpotence condition. -/
theorem elementFactorCocycle_differences_zero {G : Type*} [Group G] [Group.IsNilpotent G]
    (a : G) (n : ℕ) (hn : Group.nilpotencyClass G ≤ n)
    (xs : List (G ⧸ elementClosure a)) (hlen : xs.length = n)
    (x : G ⧸ elementClosure a) :
    (xs.map (fun y => elementFactorAction a y-1)).prod (elementFactorCocycle a x) = 0 := by
  rw [elementFactorAction_nilpotent a n hn xs (by omega),LinearMap.zero_apply]

/-- The actual surjective polynomial cocycle map from Z[G/K]/I^(n+1). -/
noncomputable def elementPolynomialCocycle {G : Type*} [Group G] [Group.IsNilpotent G]
    (a : G) (n : ℕ) (hn : Group.nilpotencyClass G ≤ n) :
    TruncatedGroupRing (G ⧸ elementClosure a) (n+1) →+ ElementCocycleModule a :=
  truncatedCocycleMap (elementFactorCocycle_identity a) n
    (elementFactorCocycle_differences_zero a n hn)

@[simp] theorem elementPolynomialCocycle_element {G : Type*} [Group G] [Group.IsNilpotent G]
    (a : G) (n : ℕ) (hn : Group.nilpotencyClass G ≤ n) (g : G) :
    elementPolynomialCocycle a n hn
      (truncatedElement (G ⧸ elementClosure a) (n+1) (QuotientGroup.mk' (elementClosure a) g)) =
    (elementDifferenceRange a).mkQ (elementCocycle a g) :=
  truncatedCocycleMap_element _ _ _ _

theorem elementPolynomialCocycle_surjective {G : Type*} [Group G] [Group.IsNilpotent G]
    (a : G) (n : ℕ) (hn : Group.nilpotencyClass G ≤ n) :
    Function.Surjective (elementPolynomialCocycle a n hn) :=
  truncatedCocycleMap_surjective _ _ _ (elementFactorCocycle_generates a)

end DirectedCycles
