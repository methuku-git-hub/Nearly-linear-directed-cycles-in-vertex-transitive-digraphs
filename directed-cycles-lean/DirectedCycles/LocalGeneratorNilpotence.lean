import DirectedCycles.LocalIteratedGeneratorCommutators

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles
namespace LocalGroupAlgebra

/-- In a genuine group, the actual local commutator relation is exactly the
usual iterated generator-commutator set. -/
theorem ofGroup_generatorCommutators_iff {G : Type*} [Group G] (S : Set G) (n : ℕ) (x : G) :
    (ofGroup G).GeneratorCommutators S n x ↔ x ∈ iteratedGeneratorCommutators S n := by
  induction n generalizing x with
  | zero =>
    constructor
    · intro h
      cases h with
      | base hx => exact hx
    · exact fun hx => .base hx
  | succ n ih =>
    constructor
    · intro h
      cases h with
      | @step _ a b _ ha hb hp =>
        have he := (ofGroup_product_iff G _ x).1 hp
        have he' : ⁅a,b⁆ = x := by
          simpa only [ofGroup,List.prod_cons,List.prod_nil,_root_.mul_one,commutatorElement_def,_root_.mul_assoc] using he.symm
        exact ⟨a,(ih a).1 ha,b,hb,he'⟩
    · rintro ⟨a,ha,b,hb,rfl⟩
      apply GeneratorCommutators.step ((ih a).2 ha) hb
      apply (ofGroup_product_iff G _ _).2
      simp only [ofGroup,List.prod_cons,List.prod_nil,_root_.mul_one,commutatorElement_def,_root_.mul_assoc]
end LocalGroupAlgebra

/-- Vanishing of the checked local generator relations supplies genuine
global nilpotence and its class bound. -/
theorem nilpotent_of_local_generator_commutators {G : Type*} [Group G]
    (S : Set G) (hgen : Subgroup.closure S = ⊤) (c : ℕ)
    (hvanish : ∀ x, (LocalGroupAlgebra.ofGroup G).GeneratorCommutators S c x → x = 1) :
    ∃ _hNil : Group.IsNilpotent G, Group.nilpotencyClass G ≤ c := by
  have hv : iteratedGeneratorCommutators S c ⊆ ({1} : Set G) := by
    intro x hx
    exact hvanish x ((LocalGroupAlgebra.ofGroup_generatorCommutators_iff S c x).2 hx)
  have hbot : lowerSeries G c = ⊥ := by
    rw [← normalClosure_iteratedGeneratorCommutators S hgen c]
    exact Subgroup.normalClosure_eq_bot_iff.mpr hv
  have hnil : Group.IsNilpotent G := Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨c,hbot⟩
  exact ⟨hnil,Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hbot⟩
end DirectedCycles
