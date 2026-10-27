module

public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Algebraic part of a symmetric local group. Multiplication is a functional
relation so that undefined products cannot accidentally be used as elements.
Associativity applies only when both bracketings are defined. -/
structure LocalGroupAlgebra (G : Type*) where
  one : G
  inv : G → G
  mulRel : G → G → G → Prop
  unique : ∀ {a b c d}, mulRel a b c → mulRel a b d → c = d
  one_mul : ∀ a, mulRel one a a
  mul_one : ∀ a, mulRel a one a
  inv_mul : ∀ a, mulRel (inv a) a one
  mul_inv : ∀ a, mulRel a (inv a) one
  assoc : ∀ {a b c ab bc x y}, mulRel a b ab → mulRel b c bc →
    mulRel ab c x → mulRel a bc y → x = y

namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

def Defined (a b : G) : Prop := ∃ c, L.mulRel a b c

noncomputable def mul (a b : G) (h : L.Defined a b) : G := Classical.choose h

theorem mul_spec (a b : G) (h : L.Defined a b) : L.mulRel a b (L.mul a b h) :=
  Classical.choose_spec h

theorem mul_eq_of_rel {a b c : G} (h : L.mulRel a b c) : L.mul a b ⟨c,h⟩ = c :=
  L.unique (L.mul_spec _ _ _) h

theorem inv_one : L.inv L.one = L.one :=
  L.unique (L.one_mul (L.inv L.one)) (L.mul_inv L.one)

theorem right_inverse_unique {a b : G} (h : L.mulRel a b L.one) : b = L.inv a :=
  L.assoc (L.inv_mul a) h (L.one_mul b) (L.mul_one (L.inv a))

theorem inv_inv (a : G) : L.inv (L.inv a) = a :=
  (L.right_inverse_unique (L.inv_mul a)).symm

theorem inv_injective : Function.Injective L.inv := by
  intro a b h
  have := congrArg L.inv h
  simpa only [L.inv_inv] using this

/-- Cancellation is valid when the inverse multiplication required for the
cancellation is defined; no global domain closure is silently assumed. -/
theorem inverse_cancel_left {a b c d : G} (hab : L.mulRel a b c)
    (hic : L.mulRel (L.inv a) c d) : d = b :=
  (L.assoc (L.inv_mul a) hab (L.one_mul b) hic).symm

theorem inverse_cancel_right {a b c d : G} (hab : L.mulRel a b c)
    (hic : L.mulRel c (L.inv b) d) : d = a :=
  L.assoc hab (L.mul_inv b) hic (L.mul_one a)

/-- Restriction to a symmetric set containing the identity gives a local group,
with multiplication defined precisely when the result stays in that set. -/
def restrict (S : Set G) (h1 : L.one ∈ S) (hi : ∀ x ∈ S, L.inv x ∈ S) : LocalGroupAlgebra S where
  one := ⟨L.one,h1⟩
  inv x := ⟨L.inv x.val,hi x.val x.property⟩
  mulRel x y z := L.mulRel x.val y.val z.val
  unique h h' := Subtype.ext (L.unique h h')
  one_mul x := L.one_mul x.val
  mul_one x := L.mul_one x.val
  inv_mul x := L.inv_mul x.val
  mul_inv x := L.mul_inv x.val
  assoc h₁ h₂ h₃ h₄ := Subtype.ext (L.assoc h₁ h₂ h₃ h₄)

theorem restrict_mulRel (S : Set G) (h1 : L.one ∈ S) (hi : ∀ x ∈ S, L.inv x ∈ S)
    (x y z : S) : (L.restrict S h1 hi).mulRel x y z ↔ L.mulRel x.val y.val z.val := Iff.rfl

/-- A global group gives a local group with every multiplication defined. -/
def ofGroup (G : Type*) [Group G] : LocalGroupAlgebra G where
  one := 1
  inv := Inv.inv
  mulRel a b c := a*b = c
  unique h h' := h.symm.trans h'
  one_mul a := _root_.one_mul a
  mul_one a := _root_.mul_one a
  inv_mul a := inv_mul_cancel a
  mul_inv a := mul_inv_cancel a
  assoc := by
    intro a b c ab bc x y hab hbc hx hy
    rw [← hab] at hx
    rw [← hbc] at hy
    exact hx.symm.trans ((mul_assoc a b c).trans hy)

theorem ofGroup_defined (G : Type*) [Group G] (a b : G) : (ofGroup G).Defined a b :=
  ⟨a*b,rfl⟩

theorem ofGroup_mul (G : Type*) [Group G] (a b : G) (h : (ofGroup G).Defined a b) :
    (ofGroup G).mul a b h = a*b :=
  (ofGroup G).unique ((ofGroup G).mul_spec a b h) rfl

/-- Global cancellation is an additional local property, rather than an
unjustified consequence of the restricted associativity axiom. -/
structure Cancellative : Prop where
  left_cancel : ∀ {a b c d}, L.mulRel a b d → L.mulRel a c d → b = c
  right_cancel : ∀ {a b c d}, L.mulRel b a d → L.mulRel c a d → b = c
  inv_product : ∀ {a b c d}, L.mulRel a b c → L.mulRel (L.inv b) (L.inv a) d → L.inv c = d

theorem ofGroup_cancellative (G : Type*) [Group G] : (ofGroup G).Cancellative where
  left_cancel h h' := mul_left_cancel (h.trans h'.symm)
  right_cancel h h' := mul_right_cancel (h.trans h'.symm)
  inv_product := by
    intro a b c d hc hd
    change c⁻¹ = d
    rw [← hc,mul_inv_rev]
    exact hd

theorem Cancellative.restrict (hL : L.Cancellative) (S : Set G) (h1 : L.one ∈ S)
    (hi : ∀ x ∈ S, L.inv x ∈ S) : (L.restrict S h1 hi).Cancellative where
  left_cancel h h' := Subtype.ext (hL.left_cancel h h')
  right_cancel h h' := Subtype.ext (hL.right_cancel h h')
  inv_product h h' := Subtype.ext (hL.inv_product h h')
end LocalGroupAlgebra
end DirectedCycles
