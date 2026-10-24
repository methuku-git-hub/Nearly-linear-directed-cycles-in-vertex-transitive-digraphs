import DirectedCycles.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.QuotientGroup.Simple

set_option autoImplicit false
namespace DirectedCycles

/-- A normal maximal subgroup has a simple quotient, even when the ambient
group is not commutative. -/
theorem simple_quotient_of_normal_coatom {G : Type*} [Group G]
    (M : Subgroup G) [M.Normal] (hM : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  have hs : IsSimpleOrder (Subgroup (G ⧸ M)) := by
    rw [(QuotientGroup.comapMk'OrderIso M).isSimpleOrder_iff]
    exact Set.isSimpleOrder_Ici_iff_isCoatom.mpr hM
  let := hs
  have hnt : Nontrivial (G ⧸ M) := by
    by_contra h
    have : Subsingleton (G ⧸ M) := not_nontrivial_iff_subsingleton.mp h
    have he : (⊥ : Subgroup (G ⧸ M)) = ⊤ := Subsingleton.elim _ _
    exact bot_ne_top he
  let := hnt
  exact ⟨fun K _ => eq_bot_or_eq_top K⟩

/-- Every maximal subgroup of a finite nilpotent group contains its
commutator subgroup. -/
theorem nilpotent_commutator_le_coatom {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] (M : Subgroup G) (hM : IsCoatom M) : commutator G ≤ M := by
  let : M.Normal := Subgroup.NormalizerCondition.normal_of_coatom M
    (Group.normalizerCondition_of_isNilpotent (G := G)) hM
  let := simple_quotient_of_normal_coatom M hM
  have : IsMulCommutative (G ⧸ M) := inferInstance
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance

/-- The Frattini generation criterion used in the manuscript, proved for
finite nilpotent groups. -/
theorem nilpotent_commutator_nongenerating {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] (U : Subgroup G) (hU : U ⊔ commutator G = ⊤) : U = ⊤ := by
  rcases eq_top_or_exists_le_coatom U with h | ⟨M, hM, hUM⟩
  · exact h
  · have hle : U ⊔ commutator G ≤ M := sup_le hUM (nilpotent_commutator_le_coatom M hM)
    rw [hU] at hle
    exact False.elim (hM.ne_top (top_le_iff.mp hle))

end DirectedCycles
