import DirectedCycles.NormalClosureCommutators
import DirectedCycles.CommutatorWords
import DirectedCycles.QuotientPowerContainment
import Mathlib.GroupTheory.Subgroup.Centralizer

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- Commutators with both entries restricted to designated generating sets. -/
def generatorCommutatorValues {G : Type*} [Group G] (T S : Set G) : Set G :=
  {z | ∃ t ∈ T, ∃ s ∈ S, ⁅t,s⁆ = z}

/-- For a generating set S, commutators against S already normally generate
all commutators against the ambient group. -/
theorem normalClosure_generatorCommutatorValues {G : Type*} [Group G]
    (T S : Set G) (hS : Subgroup.closure S = ⊤) :
    Subgroup.normalClosure (generatorCommutatorValues T S) =
      ⁅Subgroup.normalClosure T,(⊤ : Subgroup G)⁆ := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro z ⟨t,ht,s,_hs,rfl⟩
    exact Subgroup.commutator_mem_commutator (Subgroup.subset_normalClosure ht) (Subgroup.mem_top s)
  · let L := Subgroup.normalClosure (generatorCommutatorValues T S)
    let q := QuotientGroup.mk' L
    have hq := QuotientGroup.mk'_surjective L
    have hqgen : Subgroup.closure (q '' S) = ⊤ := image_generating_set q hq S hS
    have ht : q '' T ⊆ Subgroup.center (G ⧸ L) := by
      rintro z ⟨t,ht,rfl⟩
      have hc : q t ∈ Subgroup.centralizer (q '' S) := by
        apply Subgroup.mem_centralizer_iff_commutator_eq_one'.mpr
        rintro y ⟨s,hs,rfl⟩
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).mpr
          (Subgroup.subset_normalClosure (show ⁅t,s⁆ ∈ generatorCommutatorValues T S from ⟨t,ht,s,hs,rfl⟩))
      rwa [← Subgroup.centralizer_closure,hqgen,Subgroup.coe_top,Subgroup.centralizer_univ] at hc
    have hc : (Subgroup.normalClosure T).map q ≤ Subgroup.center (G ⧸ L) := by
      rw [Subgroup.map_normalClosure T q hq]
      exact Subgroup.normalClosure_le_normal ht
    have hz : (⁅Subgroup.normalClosure T,(⊤ : Subgroup G)⁆).map q = ⊥ := by
      rw [Subgroup.map_commutator,Subgroup.map_top_of_surjective q hq]
      exact Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hc
    have h := (Subgroup.map_eq_bot_iff _).mp hz
    rwa [QuotientGroup.ker_mk'] at h

def iteratedGeneratorCommutators {G : Type*} [Group G] (S : Set G) : ℕ → Set G
  | 0 => S
  | n+1 => generatorCommutatorValues (iteratedGeneratorCommutators S n) S

theorem normalClosure_iteratedGeneratorCommutators {G : Type*} [Group G]
    (S : Set G) (hS : Subgroup.closure S = ⊤) (n : ℕ) :
    Subgroup.normalClosure (iteratedGeneratorCommutators S n) = lowerSeries G n := by
  induction n with
  | zero =>
    apply top_unique
    rw [← hS]
    exact Subgroup.closure_le_normalClosure
  | succ n ih =>
    rw [iteratedGeneratorCommutators,normalClosure_generatorCommutatorValues _ S hS,ih]
    rfl

theorem generator_commutators_are_words {α G : Type*} [Group G] (x : α → G) (n : ℕ) :
    iteratedGeneratorCommutators (Set.range x) n ⊆
      {z | ∃ w : CommutatorWord α, w.weight = n+1 ∧ w.eval x = z} := by
  induction n with
  | zero =>
    rintro z ⟨i,rfl⟩
    exact ⟨.var i,rfl,rfl⟩
  | succ n ih =>
    rintro z ⟨t,ht,s,⟨i,rfl⟩,rfl⟩
    obtain ⟨w,hw,rfl⟩ := ih ht
    exact ⟨.bracket w (.var i),by simp only [CommutatorWord.weight,hw],rfl⟩

/-- Nilpotence follows from the actual commutator identities on a
generating tuple; it is not an additional structural assumption. -/
theorem nilpotent_of_generator_commutator_words {α G : Type*} [Group G]
    (x : α → G) (hgen : Subgroup.closure (Set.range x) = ⊤) (c : ℕ)
    (hwords : ∀ w : CommutatorWord α, w.weight = c+1 → w.eval x = 1) :
    ∃ _hNil : Group.IsNilpotent G, Group.nilpotencyClass G ≤ c := by
  have hv : iteratedGeneratorCommutators (Set.range x) c ⊆ ({1} : Set G) := by
    intro g hg
    obtain ⟨w,hw,rfl⟩ := generator_commutators_are_words x c hg
    exact hwords w hw
  have hbot : lowerSeries G c = ⊥ := by
    rw [← normalClosure_iteratedGeneratorCommutators (Set.range x) hgen c]
    exact Subgroup.normalClosure_eq_bot_iff.mpr hv
  have hnil : Group.IsNilpotent G := Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨c,hbot⟩
  exact ⟨hnil,Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hbot⟩

end DirectedCycles
