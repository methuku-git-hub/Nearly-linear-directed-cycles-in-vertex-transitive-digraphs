module

public import DirectedCycles.CayleyWords
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Order.Minimal

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A nontrivial finite generated group has an available generator whose
removal from an inclusion-minimal generating subset leaves a proper subgroup. -/
theorem minimal_generator_removal {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (S : Set G) (hgen : Subgroup.closure S = ⊤) :
    ∃ (a : G) (T : Finset G), a ∈ S ∧ (T : Set G) ⊆ S ∧
      Subgroup.closure (T : Set G) ≠ ⊤ ∧
      Subgroup.closure (insert a (T : Set G)) = ⊤ := by
  classical
  obtain ⟨U,hU,hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun U : Finset G => Subgroup.closure (U : Set G) = ⊤)
    S.toFinite.toFinset (by simpa only [Set.Finite.coe_toFinset] using hgen)
  have hUne : U.Nonempty := by
    by_contra he
    have hu : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have heq : (⊥ : Subgroup G) = ⊤ := by simpa only [hu,Finset.coe_empty,Subgroup.closure_empty] using hmin.1
    exact bot_ne_top heq
  obtain ⟨a,ha⟩ := hUne
  refine ⟨a,U.erase a,?_,?_,?_,?_⟩
  · exact S.toFinite.mem_toFinset.mp (hU ha)
  · intro x hx
    exact S.toFinite.mem_toFinset.mp (hU (Finset.mem_of_mem_erase hx))
  · intro he
    have heq := hmin.eq_of_ge he (Finset.erase_subset a U)
    have : a ∈ U.erase a := heq ▸ ha
    exact Finset.notMem_erase a U this
  · simpa only [← Finset.coe_insert,Finset.insert_erase ha] using hmin.1

/-- Removing one generator in an abelian group leaves a cyclic quotient,
with exactly that generator as its distinguished generator. -/
theorem quotient_generated_by_remaining_label {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal] (a : G)
    (hgen : H ⊔ Subgroup.zpowers a = ⊤) :
    Subgroup.zpowers (QuotientGroup.mk' H a) = ⊤ := by
  have he := congrArg (Subgroup.map (QuotientGroup.mk' H)) hgen
  simpa [Subgroup.map_sup,QuotientGroup.map_mk'_self,
    MonoidHom.map_zpowers,Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective H)] using he

end DirectedCycles
