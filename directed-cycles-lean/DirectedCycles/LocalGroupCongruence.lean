module

public import DirectedCycles.LocalGroupHom

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A congruence for a partial group must transport product domains as well
as product values. This requirement prevents quotienting from inventing
products whose representatives cannot be chosen consistently. -/
structure LocalGroupCongruence {G : Type*} (L : LocalGroupAlgebra G) where
  toSetoid : Setoid G
  inv_rel : ∀ {a b}, toSetoid.r a b → toSetoid.r (L.inv a) (L.inv b)
  mul_lift : ∀ {a b c a' b'}, L.mulRel a b c → toSetoid.r a a' → toSetoid.r b b' →
    ∃ c', L.mulRel a' b' c' ∧ toSetoid.r c c'

namespace LocalGroupCongruence
variable {G : Type*} {L : LocalGroupAlgebra G} (C : LocalGroupCongruence L)

abbrev Carrier := Quotient C.toSetoid
abbrev project (a : G) : C.Carrier := Quotient.mk C.toSetoid a

def inv : C.Carrier → C.Carrier := Quotient.map L.inv (fun _ _ h => C.inv_rel h)

def mulRel (x y z : C.Carrier) : Prop :=
  ∃ a b c : G, C.project a = x ∧ C.project b = y ∧ C.project c = z ∧ L.mulRel a b c

/-- Every quotient multiplication lifts using any prescribed pair of source
representatives, because the congruence explicitly preserves its domain. -/
theorem lift_mul {a b : G} {z : C.Carrier} (h : C.mulRel (C.project a) (C.project b) z) :
    ∃ c : G, C.project c = z ∧ L.mulRel a b c := by
  obtain ⟨a',b',c',ha,hb,hc,hm⟩ := h
  obtain ⟨c,hm',hc'⟩ := C.mul_lift hm (Quotient.exact ha) (Quotient.exact hb)
  exact ⟨c,(Quotient.sound hc').symm.trans hc,hm'⟩

/-- The quotient is an actual partial group, with associativity proved by
lifting every relevant multiplication to one consistent set of representatives. -/
def algebra : LocalGroupAlgebra C.Carrier where
  one := C.project L.one
  inv := C.inv
  mulRel := C.mulRel
  unique := by
    intro a b c d
    refine Quotient.inductionOn₂ a b ?_
    intro a b hc hd
    obtain ⟨x,hx,hmx⟩ := C.lift_mul hc
    obtain ⟨y,hy,hmy⟩ := C.lift_mul hd
    exact hx.symm.trans ((congrArg C.project (L.unique hmx hmy)).trans hy)
  one_mul := by
    intro a
    refine Quotient.inductionOn a ?_
    intro a
    exact ⟨L.one,a,a,rfl,rfl,rfl,L.one_mul a⟩
  mul_one := by
    intro a
    refine Quotient.inductionOn a ?_
    intro a
    exact ⟨a,L.one,a,rfl,rfl,rfl,L.mul_one a⟩
  inv_mul := by
    intro a
    refine Quotient.inductionOn a ?_
    intro a
    exact ⟨L.inv a,a,L.one,rfl,rfl,rfl,L.inv_mul a⟩
  mul_inv := by
    intro a
    refine Quotient.inductionOn a ?_
    intro a
    exact ⟨a,L.inv a,L.one,rfl,rfl,rfl,L.mul_inv a⟩
  assoc := by
    intro a b c ab bc x y
    refine Quotient.inductionOn₃ a b c ?_
    intro a b c hab hbc hx hy
    obtain ⟨ab',hab',hmab⟩ := C.lift_mul hab
    obtain ⟨bc',hbc',hmbc⟩ := C.lift_mul hbc
    obtain ⟨x',hx',hmx⟩ := C.lift_mul (a := ab') (b := c) (by simpa only [hab'] using hx)
    obtain ⟨y',hy',hmy⟩ := C.lift_mul (a := a) (b := bc') (by simpa only [hbc'] using hy)
    exact hx'.symm.trans ((congrArg C.project (L.assoc hmab hmbc hmx hmy)).trans hy')

def projectionHom : LocalGroupHom L C.algebra where
  toFun := C.project
  map_one := rfl
  map_inv _ := rfl
  map_mul := fun {a b c} h => ⟨a,b,c,rfl,rfl,rfl,h⟩
end LocalGroupCongruence
end DirectedCycles
