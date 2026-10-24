import DirectedCycles.Augmentation
import Mathlib.Algebra.Group.Subgroup.Map

set_option autoImplicit false
open scoped MonoidAlgebra
namespace DirectedCycles

/-- The augmentation ideal is generated additively by differences g-1. -/
theorem augmentation_ideal_generated {G : Type*} [Group G] :
    (augmentationIdeal G).toAddSubgroup =
      AddSubgroup.closure (Set.range (fun g : G => MonoidAlgebra.of ℤ G g - 1)) := by
  let W := AddSubgroup.closure (Set.range (fun g : G => MonoidAlgebra.of ℤ G g - 1))
  have hres : ∀ x : ℤ[G], x - augmentation G x • (1 : ℤ[G]) ∈ W := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      rw [augmentation_of,one_zsmul]
      exact AddSubgroup.subset_closure ⟨g,rfl⟩
    | add x y hx hy =>
      rw [map_add,add_zsmul]
      have he : x+y-(augmentation G x • (1 : ℤ[G])+augmentation G y • 1) =
          (x-augmentation G x • 1)+(y-augmentation G y • 1) := by abel
      rw [he]
      exact W.add_mem hx hy
    | smul z x hx =>
      rw [map_zsmul,smul_eq_mul,← smul_smul,← smul_sub]
      exact W.zsmul_mem hx z
  apply le_antisymm
  · intro x hx
    change augmentation G x = 0 at hx
    simpa only [hx,zero_zsmul,sub_zero] using hres x
  · apply (augmentationIdeal G).toAddSubgroup.closure_le.mpr
    rintro x ⟨g,rfl⟩
    exact group_difference_mem_augmentation g

/-- Bilinearity extends a product inclusion from additive generators to
the generated additive subgroups. -/
theorem additive_closure_mul {R : Type*} [Ring R] (S T : Set R) (W : AddSubgroup R)
    (h : ∀ a ∈ S, ∀ b ∈ T, a*b ∈ W)
    {a b : R} (ha : a ∈ AddSubgroup.closure S) (hb : b ∈ AddSubgroup.closure T) : a*b ∈ W := by
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
    induction hb using AddSubgroup.closure_induction with
    | mem b hb => exact h a ha b hb
    | zero => simpa only [mul_zero] using W.zero_mem
    | add x y _ _ hx hy => simpa only [mul_add] using W.add_mem hx hy
    | neg x _ hx => simpa only [mul_neg] using W.neg_mem hx
  | zero => simpa only [zero_mul] using W.zero_mem
  | add x y _ _ hx hy => simpa only [add_mul] using W.add_mem hx hy
  | neg x _ hx => simpa only [neg_mul] using W.neg_mem hx

noncomputable def groupDifferenceWord {G : Type*} [Group G] (gs : List G) : ℤ[G] :=
  (gs.map (fun g => MonoidAlgebra.of ℤ G g - 1)).prod

/-- Every positive ideal power is exactly the additive span of ordered
products of the required number of differences. -/
theorem augmentation_power_generated {G : Type*} [Group G] (n : ℕ) :
    (augmentationIdeal G ^ (n+1)).toAddSubgroup =
      AddSubgroup.closure {x | ∃ gs : List G, gs.length = n+1 ∧ groupDifferenceWord gs = x} := by
  induction n with
  | zero =>
    rw [show (0+1 : ℕ) = 1 from rfl,Submodule.pow_one,augmentation_ideal_generated]
    congr 1
    ext x
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨[g],rfl,by simp [groupDifferenceWord]⟩
    · rintro ⟨gs,hgs,rfl⟩
      obtain ⟨g,rfl⟩ := List.length_eq_one_iff.mp hgs
      exact ⟨g,by simp [groupDifferenceWord]⟩
  | succ n ih =>
    let W := AddSubgroup.closure {x | ∃ gs : List G, gs.length = n+1+1 ∧ groupDifferenceWord gs = x}
    apply le_antisymm
    · intro x hx
      change x ∈ augmentationIdeal G ^ (n+1+1) at hx
      rw [Submodule.pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        change a ∈ (augmentationIdeal G ^ (n+1)).toAddSubgroup at ha
        change b ∈ (augmentationIdeal G).toAddSubgroup at hb
        rw [ih] at ha
        rw [augmentation_ideal_generated] at hb
        apply additive_closure_mul _ _ W _ ha hb
        rintro a ⟨gs,hlen,rfl⟩ b ⟨g,rfl⟩
        exact AddSubgroup.subset_closure ⟨gs++[g],by simp [hlen],by
          simp [groupDifferenceWord,List.map_append,List.prod_append]⟩
      · intro a b ha hb
        exact W.add_mem ha hb
    · apply (augmentationIdeal G ^ (n+1+1)).toAddSubgroup.closure_le.mpr
      rintro x ⟨gs,hlen,rfl⟩
      have h := list_prod_mem_augmentation_power
        (gs.map (fun g => MonoidAlgebra.of ℤ G g - 1)) (by
          intro y hy
          obtain ⟨g,_,rfl⟩ := List.mem_map.mp hy
          exact group_difference_mem_augmentation g)
      change groupDifferenceWord gs ∈ augmentationIdeal G ^ (n+1+1)
      simpa only [List.length_map,hlen,groupDifferenceWord] using h

end DirectedCycles
