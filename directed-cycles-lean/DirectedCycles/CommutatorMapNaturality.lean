import DirectedCycles.CommutatorWordBounds
import DirectedCycles.NormalClosureCommutators

set_option autoImplicit false
open scoped commutatorElement Pointwise
namespace DirectedCycles

theorem CommutatorWord.eval_map {α G Q : Type*} [Group G] [Group Q]
    (w : CommutatorWord α) (f : G →* Q) (x : α → G) :
    w.eval (fun i => f (x i)) = f (w.eval x) := by
  induction w with
  | var _ => rfl
  | bracket a b ha hb =>
    simp only [CommutatorWord.eval,ha,hb,map_commutatorElement]

theorem MarkedCommutatorWord.eval_map {α G Q : Type*} [Group G] [Group Q]
    (w : MarkedCommutatorWord α) (f : G →* Q) (h : G) (x : α → G) :
    w.eval (f h) (fun i => f (x i)) = f (w.eval h x) := by
  induction w with
  | marked => rfl
  | left a b ha =>
    simp only [MarkedCommutatorWord.eval,ha,b.eval_map,map_commutatorElement]
  | right a b hb =>
    simp only [MarkedCommutatorWord.eval,hb,a.eval_map,map_commutatorElement]

/-- Short terminal values in any quotient lift to short central values in
the original group. This identifies their membership in the bounded-rank
subgroup obtained from the first central quotient. -/
theorem MarkedCommutatorWord.short_values_lift {α G Q : Type*} [Group G] [Group Q]
    (w : MarkedCommutatorWord α) (f : G →* Q) (H : Subgroup G)
    (A : Set G) (h1 : 1 ∈ A) (hi : A⁻¹ = A) (hH : (H : Set G) ⊆ A)
    (hnext : relativeSeries (Subgroup.normalClosure (H : Set G)) (w.degree+1) = ⊥)
    (h : Q) (hh : h ∈ H.map f) (x : α → Q) (hx : ∀ i, x i ∈ (f '' A)^4) :
    w.eval h x ∈ f '' (A^(4^(w.degree+1)*4) ∩ (Subgroup.center G : Set G)) := by
  classical
  obtain ⟨a,ha,rfl⟩ := hh
  have hlift : ∀ i, ∃ g ∈ A^4, f g = x i := by
    intro i
    have ht := hx i
    rwa [← Set.image_pow] at ht
  choose y hy he using hlift
  refine ⟨w.eval a y,⟨?_,?_⟩,?_⟩
  · exact w.eval_mem_power a y A h1 hi 4 (Set.subset_pow h1 (by norm_num : 4 ≠ 0) (hH ha)) hy
  · exact relativeSeries_central_of_next_eq_bot _ _ hnext
      (w.eval_mem_relativeSeries _ a (Subgroup.subset_normalClosure ha) y)
  · rw [← w.eval_map]
    congr 1
    funext i
    exact he i

end DirectedCycles
