import DirectedCycles.ActionCoordinates

set_option autoImplicit false
namespace DirectedCycles

@[instance_reducible]
def coordinateMulAction (G I : Type*) [Group G] : MulAction G (G × I) where
  smul g x := (g*x.1,x.2)
  one_smul x := Prod.ext (one_mul x.1) rfl
  mul_smul g h x := Prod.ext (mul_assoc g h x.1) rfl

theorem coordinate_action_free (G I : Type*) [Group G] :
    letI := coordinateMulAction G I
    ∀ (g : G) (x : G × I), g • x = x → g = 1 := by
  intro g x he
  have hg : g*x.1 = x.1 := congrArg Prod.fst he
  exact mul_right_cancel (hg.trans (one_mul x.1).symm)

theorem coordinate_action_orbit_count (G I : Type*) [Group G] [Finite G] :
    letI := coordinateMulAction G I
    Nat.card (Quotient (MulAction.orbitRel G (G × I))) = Nat.card I := by
  let : MulAction G (G × I) := coordinateMulAction G I
  have hcard := free_action_cardinality (coordinate_action_free G I)
  rw [Nat.card_prod] at hcard
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := G)) hcard.symm

end DirectedCycles
