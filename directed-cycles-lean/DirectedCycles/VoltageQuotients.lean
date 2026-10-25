module

public import DirectedCycles.ActionCoordinates
public import DirectedCycles.CycleLift

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

theorem voltage_left_invariant {G I : Type*} [Group G] (S : I → I → Set G)
    (g : G) (x y : G × I) :
    VoltageDigraph S (g*x.1,x.2) (g*y.1,y.2) ↔ VoltageDigraph S x y := by
  constructor
  · rintro ⟨a,ha,he⟩
    exact ⟨a,ha,mul_left_cancel (he.trans (mul_assoc _ _ _))⟩
  · rintro ⟨a,ha,he⟩
    exact ⟨a,ha,by rw [he,mul_assoc]⟩

theorem voltage_quotient_stronglyConnected {G H I : Type*} [Group G] [Group H]
    (q : G →* H) (hq : Function.Surjective q) (S : I → I → Set G)
    (hsc : StronglyConnected (VoltageDigraph S)) :
    StronglyConnected (VoltageDigraph (fun i j => q '' S i j)) := by
  let pi : G × I → H × I := fun x => (q x.1,x.2)
  have hs : Function.Surjective pi := by
    rintro ⟨h,i⟩
    obtain ⟨g,rfl⟩ := hq h
    exact ⟨(g,i),rfl⟩
  apply stronglyConnected_image pi hs _ hsc
  rintro x y ⟨a,ha,he⟩
  exact ⟨q a,⟨a,ha,rfl⟩,by change q y.1=q x.1*q a; rw [he,map_mul]⟩

/-- Every cycle in a quotient voltage graph lifts through explicit bijections
between its consecutive fibres. No choice of a matching is assumed. -/
theorem voltage_quotient_cycle_lift {G H I : Type*} [Group G] [Group H]
    [Finite G] [Finite I] (q : G →* H) (hq : Function.Surjective q) (S : I → I → Set G)
    (Q : Cycle (VoltageDigraph (fun i j => q '' S i j))) :
    ∃ C : Cycle (VoltageDigraph S), Q.length ≤ C.length := by
  classical
  let : Fintype (G × I) := Fintype.ofFinite _
  let pi : G × I → H × I := fun x => (q x.1,x.2)
  have hschoose : ∀ i, ∃ s ∈ S (Q.vertex i).2 (Q.vertex (finRotate Q.length i)).2,
      (Q.vertex (finRotate Q.length i)).1 = (Q.vertex i).1*q s := by
    intro i
    obtain ⟨a,⟨s,hs,rfl⟩,he⟩ := Q.arc i
    exact ⟨s,hs,he⟩
  choose s hs hstep using hschoose
  have hsur : Function.Surjective pi := by
    rintro ⟨h,i⟩
    obtain ⟨g,rfl⟩ := hq h
    exact ⟨(g,i),rfl⟩
  apply cycle_lift_of_fibre_matchings pi Q (fun i => hsur (Q.vertex i))
  intro i
  let e : {x // pi x = Q.vertex i} ≃ {y // pi y = Q.vertex (finRotate Q.length i)} := {
    toFun := fun x => ⟨(x.val.1*s i,(Q.vertex (finRotate Q.length i)).2),by
      apply Prod.ext
      · change q (x.val.1*s i) = (Q.vertex (finRotate Q.length i)).1
        rw [map_mul,show q x.val.1 = (Q.vertex i).1 from congrArg Prod.fst x.property,← hstep]
      · rfl⟩
    invFun := fun y => ⟨(y.val.1*(s i)⁻¹,(Q.vertex i).2),by
      apply Prod.ext
      · change q (y.val.1*(s i)⁻¹) = (Q.vertex i).1
        rw [map_mul,map_inv,show q y.val.1 = (Q.vertex (finRotate Q.length i)).1 from
          congrArg Prod.fst y.property,hstep,mul_inv_cancel_right]
      · rfl⟩
    left_inv := fun x => Subtype.ext (Prod.ext (mul_inv_cancel_right _ _)
      (congrArg Prod.snd x.property).symm)
    right_inv := fun y => Subtype.ext (Prod.ext (inv_mul_cancel_right _ _)
      (congrArg Prod.snd y.property).symm) }
  refine ⟨e,?_⟩
  intro x
  refine ⟨s i,?_,rfl⟩
  change s i ∈ S x.val.2 (Q.vertex (finRotate Q.length i)).2
  rw [congrArg Prod.snd x.property]
  exact hs i

end DirectedCycles
