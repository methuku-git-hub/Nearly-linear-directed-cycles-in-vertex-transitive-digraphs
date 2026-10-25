module

public import DirectedCycles.LocalGeneratorNilpotence
public import DirectedCycles.CosetProgressionFromLeftCommutators
public import DirectedCycles.LeftGeneratorCommutatorMaps
public import DirectedCycles.LocalOrderedGrid

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- A tuple generates its closure as a subgroup in its own right. -/
theorem tuple_generates_its_closure {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    Subgroup.closure (Set.range (fun i =>
      (⟨g i,Subgroup.subset_closure (Set.mem_range_self i)⟩ : Subgroup.closure (Set.range g)))) = ⊤ := by
  let U := Subgroup.closure (Set.range g)
  have he : Set.range (fun i => (⟨g i,Subgroup.subset_closure (Set.mem_range_self i)⟩ : U)) =
      U.subtype ⁻¹' Set.range g := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,hi⟩
      exact ⟨i,Subtype.ext hi⟩
  rw [he]
  exact Subgroup.closure_preimage_eq_top (Set.range g)

/-- Construct the actual global nilprogression from the ambient local
commutator laws; nilpotence is derived, not stored as an extra premise. -/
def nilprogressionOfAmbientCommutators {G : Type*} [Group G] {r c : ℕ}
    (g : Fin r → G) (N : Fin r → ℕ) (hN : ∀ i, 1 ≤ N i)
    (hvanish : ∀ x, (LocalGroupAlgebra.ofGroup G).GeneratorCommutators (Set.range g) c x → x = 1) :
    CosetNilprogression G r c := by
  let U := Subgroup.closure (Set.range g)
  let gu : Fin r → U := fun i => ⟨g i,Subgroup.subset_closure (Set.mem_range_self i)⟩
  have hgen : Subgroup.closure (((⊥ : Subgroup G).subgroupOf U : Set U) ∪ Set.range gu) = ⊤ := by
    apply top_unique
    rw [← tuple_generates_its_closure g]
    exact Subgroup.closure_mono Set.subset_union_right
  apply cosetNilprogressionOfLeftCommutators U ⊥ bot_le inferInstance gu N hN hgen
  intro i l hl
  have hsource : leftGeneratorCommutator g i l = 1 := by
    apply hvanish
    apply (LocalGroupAlgebra.ofGroup_generatorCommutators_iff (Set.range g) c _).2
    rw [← hl]
    exact leftGeneratorCommutator_mem g i l
  have hu : leftGeneratorCommutator gu i l = 1 := by
    apply Subtype.ext
    have hh := map_leftGeneratorCommutator U.subtype gu i l
    change (leftGeneratorCommutator gu i l).val = leftGeneratorCommutator g i l at hh
    exact hh.trans hsource
  rw [← map_leftGeneratorCommutator,hu,map_one]

/-- With trivial finite subgroup, the constructed carrier is exactly the
actual signed-word progression in the original global group. -/
theorem nilprogressionOfAmbientCommutators_carrier {G : Type*} [Group G] {r c : ℕ}
    (g : Fin r → G) (N : Fin r → ℕ) (hN : ∀ i, 1 ≤ N i)
    (hvanish : ∀ x, (LocalGroupAlgebra.ofGroup G).GeneratorCommutators (Set.range g) c x → x = 1) :
    (nilprogressionOfAmbientCommutators g N hN hvanish).carrier =
      (LocalGroupAlgebra.ofGroup G).wordProgression g N := by
  ext z
  change (∃ h : (⊥ : Subgroup G), ∃ w : List (Fin r × Bool),
      (∀ i, w.countP (fun a => a.1 = i) ≤ N i) ∧ h.val*signedWordValue g w = z) ↔ _
  constructor
  · rintro ⟨h,w,hw,hz⟩
    have hh : h.val = 1 := h.property
    rw [hh,one_mul] at hz
    refine ⟨w,hw,?_⟩
    apply (LocalGroupAlgebra.ofGroup_product_iff G _ _).2
    exact hz.symm
  · rintro ⟨w,hw,hp⟩
    refine ⟨1,w,hw,?_⟩
    have hz := (LocalGroupAlgebra.ofGroup_product_iff G _ _).1 hp
    change 1*signedWordValue g w = z
    rw [one_mul]
    exact hz.symm
end DirectedCycles
