import DirectedCycles.BaselineClosureCongruence

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

@[simp] theorem abelian_elementCommutators {G : Type*} [CommGroup G] (a : G) :
    elementCommutators a = ⊥ := by
  apply le_antisymm
  · apply (⊥ : Subgroup G).closure_le.mpr
    rintro x ⟨g,rfl⟩
    change ⁅g,a⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm g a)
  · exact bot_le

@[simp] theorem abelian_elementClosure {G : Type*} [CommGroup G] (a : G) :
    elementClosure a = Subgroup.zpowers a := by
  simp only [elementClosure,abelian_elementCommutators,sup_bot_eq]

theorem abelian_elementCommutators_subsingleton {G : Type*} [CommGroup G] (a : G) :
    Subsingleton (elementCommutators a) := by
  rw [abelian_elementCommutators]
  infer_instance

theorem abelian_closure_factor_order {G : Type*} [CommGroup G] [Finite G] (a : G) :
    Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)) = orderOf a := by
  rw [elementClosure_factor_card_eq_orderOf]
  have hi : Function.Injective (QuotientGroup.mk' (elementCommutators a)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_mk',abelian_elementCommutators]
  exact orderOf_injective _ hi a

end DirectedCycles
