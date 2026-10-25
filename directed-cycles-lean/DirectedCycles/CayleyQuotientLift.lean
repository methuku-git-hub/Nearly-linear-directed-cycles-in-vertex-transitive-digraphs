module

public import DirectedCycles.CycleLift
public import DirectedCycles.CayleyCycleLabels

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Chosen quotient labels define bijections between consecutive fibres by
right multiplication. Their periodic orbits give a simple directed lift. -/
theorem cayley_quotient_cycle_lift {G H : Type*} [Group G] [Group H] [Finite G]
    (q : G →* H) (hq : Function.Surjective q) (S : Set G)
    (Q : Cycle (CayleyDigraph (q '' S))) :
    ∃ C : Cycle (CayleyDigraph S), Q.length ≤ C.length := by
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨s,hs,hstep⟩ := cayley_cycle_labels q S Q
  apply cycle_lift_of_fibre_matchings q Q (fun i => hq (Q.vertex i))
  intro i
  let e : {x // q x = Q.vertex i} ≃ {y // q y = Q.vertex (finRotate Q.length i)} := {
    toFun := fun x => ⟨x.val*s i,by rw [map_mul,x.property,← hstep]⟩
    invFun := fun y => ⟨y.val*(s i)⁻¹,by rw [map_mul,map_inv,y.property,hstep,mul_inv_cancel_right]⟩
    left_inv := fun x => Subtype.ext (mul_inv_cancel_right _ _)
    right_inv := fun y => Subtype.ext (inv_mul_cancel_right _ _) }
  exact ⟨e,fun x => ⟨s i,hs i,rfl⟩⟩

end DirectedCycles
