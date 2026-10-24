import DirectedCycles.CyclicResiduePowers
import DirectedCycles.RunSeparation

set_option autoImplicit false
namespace DirectedCycles

/-- A mixed return-path collision forces precisely the forbidden
difference of connector residues. -/
theorem residue_collision_difference {Q : Type*} [Group Q] (a : Q) [NeZero (orderOf a)]
    (g g' t : Q) (e v w : ZMod (orderOf a)) (u u' : ℕ)
    (hoffset : g*t*g'⁻¹ = residuePower a e)
    (hcollision : residuePower a (w+(u' : ZMod (orderOf a)))*g' =
      (residuePower a (v+(u : ZMod (orderOf a)))*g)*t) :
    w-v = e+(u : ZMod (orderOf a))-(u' : ZMod (orderOf a)) := by
  have hg : g*t = residuePower a e*g' := (mul_inv_eq_iff_eq_mul).mp hoffset
  rw [mul_assoc,hg,← mul_assoc,← residuePower_add] at hcollision
  have he := residuePower_injective a (mul_right_cancel hcollision)
  linear_combination he

theorem no_mixed_residue_collision {Q : Type*} [Group Q] (a : Q) [NeZero (orderOf a)]
    (g g' t : Q) (e v w : ZMod (orderOf a)) (D u u' : ℕ) (hu : u ≤ D) (hu' : u' ≤ D)
    (hoffset : g*t*g'⁻¹ = residuePower a e)
    (havoid : w-v ∉ collisionForbiddenResidues (orderOf a) D e) :
    residuePower a (w+(u' : ZMod (orderOf a)))*g' ≠
      (residuePower a (v+(u : ZMod (orderOf a)))*g)*t := by
  intro he
  exact collision_residue_excluded (orderOf a) D e v w havoid u u' hu hu'
    (residue_collision_difference a g g' t e v w u u' hoffset he)

/-- The two endpoint intervals at one quotient position cannot meet. -/
theorem no_source_target_residue_collision {Q : Type*} [Group Q]
    (a : Q) [NeZero (orderOf a)] (g : Q) (v : ZMod (orderOf a))
    (D l u u' : ℕ) (hl : 1 ≤ l) (hupper : l ≤ orderOf a-2*D-2)
    (hh : 2*D+2 ≤ orderOf a) (hu : u ≤ D+1) (hu' : u' ≤ D) :
    residuePower a (v+(u : ZMod (orderOf a)))*g ≠
      residuePower a (v-(l : ZMod (orderOf a))-(D : ZMod (orderOf a))+(u' : ZMod (orderOf a)))*g := by
  intro he
  have hh' := residuePower_injective a (mul_right_cancel he)
  apply separated_source_target (orderOf a) D l hl hupper hh u u' hu hu'
  linear_combination hh'

end DirectedCycles
