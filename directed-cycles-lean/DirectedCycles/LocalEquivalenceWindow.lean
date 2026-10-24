import DirectedCycles.LocalGroupAlgebra
import DirectedCycles.LocalTripleProducts
import DirectedCycles.LocalWordPowerMonotonicity

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- An equivalence on a larger local window that respects inversion and
all already-defined products. Unlike a domain-transporting congruence, it
does not assert that replacing a representative preserves the domain. -/
structure EquivalenceWindow (S : Set G) where
  Rel : G → G → Prop
  refl : ∀ x ∈ S, Rel x x
  symm : ∀ x ∈ S, ∀ y ∈ S, Rel x y → Rel y x
  trans : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, Rel x y → Rel y z → Rel x z
  inv_rel : ∀ x ∈ S, ∀ y ∈ S, Rel x y → Rel (L.inv x) (L.inv y)
  mul_rel : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ a' ∈ S, ∀ b' ∈ S, ∀ c' ∈ S,
    L.mulRel a b c → L.mulRel a' b' c' → Rel a a' → Rel b b' → Rel c c'

namespace EquivalenceWindow
variable {L} {S W : Set G} (C : L.EquivalenceWindow S) (hWS : W ⊆ S)

def setoid : Setoid W where
  r x y := C.Rel x.val y.val
  iseqv := {
    refl := fun x => C.refl x.val (hWS x.property)
    symm := by
      intro x y h
      exact C.symm x.val (hWS x.property) y.val (hWS y.property) h
    trans := by
      intro x y z h h'
      exact C.trans x.val (hWS x.property) y.val (hWS y.property) z.val (hWS z.property) h h' }

abbrev Carrier := Quotient (C.setoid hWS)
abbrev project (x : W) : C.Carrier hWS := Quotient.mk (C.setoid hWS) x

def inv (hWi : ∀ x ∈ W, L.inv x ∈ W) : C.Carrier hWS → C.Carrier hWS :=
  Quotient.map (fun x : W => ⟨L.inv x.val,hWi x.val x.property⟩)
    (fun a b h => C.inv_rel a.val (hWS a.property) b.val (hWS b.property) h)

def mulRel (x y z : C.Carrier hWS) : Prop :=
  ∃ a b c : W, C.project hWS a = x ∧ C.project hWS b = y ∧ C.project hWS c = z ∧ L.mulRel a.val b.val c.val

theorem mul_unique {x y z z' : C.Carrier hWS}
    (hz : C.mulRel hWS x y z) (hz' : C.mulRel hWS x y z') : z = z' := by
  obtain ⟨a,b,c,ha,hb,hc,hm⟩ := hz
  obtain ⟨a',b',c',ha',hb',hc',hm'⟩ := hz'
  rw [← hc,← hc']
  apply Quotient.sound
  exact C.mul_rel a.val (hWS a.property) b.val (hWS b.property) c.val (hWS c.property)
    a'.val (hWS a'.property) b'.val (hWS b'.property) c'.val (hWS c'.property) hm hm'
    (Quotient.exact (ha.trans ha'.symm)) (Quotient.exact (hb.trans hb'.symm))
end EquivalenceWindow
end LocalGroupAlgebra
end DirectedCycles
