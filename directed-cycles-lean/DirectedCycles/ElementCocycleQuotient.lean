import DirectedCycles.CocycleDescent
import DirectedCycles.ElementCocycleGeneration
import DirectedCycles.ConjugationNilpotence

set_option autoImplicit false
namespace DirectedCycles

/-- The subgroup (I-L)V in the manuscript, as an integral submodule. -/
def elementDifferenceRange {G : Type*} [Group G] (a : G) :
    Submodule ℤ (NormalAbelianModule (elementCommutators a)) :=
  LinearMap.range (1-normalAbelianAction (elementCommutators a) a)

abbrev ElementCocycleModule {G : Type*} [Group G] (a : G) :=
  NormalAbelianModule (elementCommutators a) ⧸ elementDifferenceRange a

theorem elementDifferenceRange_invariant {G : Type*} [Group G] (a : G) :
    ∀ g : G, elementDifferenceRange a ≤
      (elementDifferenceRange a).comap (normalAbelianAction (elementCommutators a) g) :=
  representation_difference_range_invariant _ a (elementCocycle_action_commute a)

/-- The ambient action on V/(I-L)V. -/
def elementQuotientAction {G : Type*} [Group G] (a : G) :
    G →* Module.End ℤ (ElementCocycleModule a) :=
  quotientRepresentation _ (elementDifferenceRange a) (elementDifferenceRange_invariant a)

/-- The actual quotient-valued commutator map before descending G/K. -/
def elementQuotientCocycle {G : Type*} [Group G] (a g : G) : ElementCocycleModule a :=
  (elementDifferenceRange a).mkQ (elementCocycle a g)

theorem elementQuotientCocycle_identity {G : Type*} [Group G] (a : G) :
    IsAdditiveCocycle (elementQuotientAction a) (elementQuotientCocycle a) :=
  quotientCocycle_identity (elementCocycle_identity a) _ (elementDifferenceRange_invariant a)

/-- The normal closure K acts trivially on V/(I-L)V. -/
theorem elementClosure_le_quotientAction_ker {G : Type*} [Group G] (a : G) :
    elementClosure a ≤ (elementQuotientAction a).ker := by
  rw [elementClosure_eq_normalClosure]
  apply Subgroup.normalClosure_le_normal
  apply Set.singleton_subset_iff.mpr
  exact quotientRepresentation_at_difference _ a (elementCocycle_action_commute a)

/-- The quotient-valued cocycle vanishes on the entire normal closure K. -/
theorem elementClosure_le_quotientCocycle_zero {G : Type*} [Group G] (a : G) :
    elementClosure a ≤ cocycleZeroSubgroup (elementQuotientCocycle_identity a) := by
  apply sup_le
  · apply Subgroup.zpowers_le.mpr
    change (elementDifferenceRange a).mkQ (elementCocycle a a) = 0
    rw [elementCocycle_self,map_zero]
  · intro b hb
    change (elementDifferenceRange a).mkQ (elementCocycle a b) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [elementCocycle_internal a ⟨b,hb⟩]
    exact ⟨normalAbelianElement _ ⟨b,hb⟩,rfl⟩

/-- The representation of the actual quotient group G/K. -/
def elementFactorAction {G : Type*} [Group G] (a : G) :
    G ⧸ elementClosure a →* Module.End ℤ (ElementCocycleModule a) :=
  QuotientGroup.lift _ (elementQuotientAction a) (elementClosure_le_quotientAction_ker a)

/-- The commutator cocycle on the actual quotient group G/K. -/
def elementFactorCocycle {G : Type*} [Group G] (a : G) :
    G ⧸ elementClosure a → ElementCocycleModule a :=
  descendedCocycle (elementQuotientCocycle_identity a) _ (elementClosure_le_quotientCocycle_zero a)

@[simp] theorem elementFactorCocycle_mk {G : Type*} [Group G] (a g : G) :
    elementFactorCocycle a (QuotientGroup.mk' (elementClosure a) g) = elementQuotientCocycle a g := rfl

@[simp] theorem elementFactorAction_mk {G : Type*} [Group G] (a g : G) :
    elementFactorAction a (QuotientGroup.mk' (elementClosure a) g) = elementQuotientAction a g := rfl

theorem elementFactorCocycle_identity {G : Type*} [Group G] (a : G) :
    IsAdditiveCocycle (elementFactorAction a) (elementFactorCocycle a) :=
  descendedCocycle_identity (elementQuotientCocycle_identity a) _
    (elementClosure_le_quotientCocycle_zero a) (elementClosure_le_quotientAction_ker a)

/-- The descended cocycle values generate the entire quotient module. -/
theorem elementFactorCocycle_generates {G : Type*} [Group G] (a : G) :
    AddSubgroup.closure (Set.range (elementFactorCocycle a)) = ⊤ := by
  have he : Set.range (elementFactorCocycle a) = Set.range (elementQuotientCocycle a) := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (elementClosure a) y
      exact ⟨g,rfl⟩
    · rintro ⟨g,rfl⟩
      exact ⟨QuotientGroup.mk' (elementClosure a) g,rfl⟩
  rw [he]
  change AddSubgroup.closure (Set.range
    (((elementDifferenceRange a).mkQ.toAddMonoidHom) ∘ elementCocycle a)) = ⊤
  rw [Set.range_comp,← AddMonoidHom.map_closure,elementCocycle_generates]
  exact AddSubgroup.map_top_of_surjective _ (elementDifferenceRange a).mkQ_surjective

end DirectedCycles
