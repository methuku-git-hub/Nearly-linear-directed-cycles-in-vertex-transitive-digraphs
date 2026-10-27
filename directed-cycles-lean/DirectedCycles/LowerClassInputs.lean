module

public import DirectedCycles.NilpotentRanks
public import DirectedCycles.ElementNormalClosure

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Every subgroup of the distinguished commutator group has the uniform
ambient generator bound and at most half the ambient nilpotency class. -/
theorem elementCommutators_subgroup_bounds {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] (a : G) (r c : ℕ) (hr : Group.rank G ≤ r)
    (hc : Group.nilpotencyClass G ≤ c) (U : Subgroup (elementCommutators a)) :
    Group.rank U ≤ ∑ i ∈ Finset.range c, r^(i+1) ∧ Group.nilpotencyClass U ≤ c/2 := by
  let B := elementCommutators a
  let e := Subgroup.equivMapOfInjective U B.subtype B.subtype_injective
  constructor
  · rw [Group.rank_congr e]
    exact nilpotent_subgroup_rank_bound r c hr hc (U.map B.subtype)
  · exact (Subgroup.nilpotencyClass_le U).trans
      (commutator_subgroup_class_le_half B (elementCommutators_le_derived a) c hc)

end DirectedCycles
