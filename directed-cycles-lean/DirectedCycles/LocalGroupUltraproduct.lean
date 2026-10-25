module

public import DirectedCycles.LocalGroupAlgebra
public import Mathlib.Order.Filter.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G : ι → Type*)

/-- Equality of dependent representatives on a filter-large set. -/
def localUltraSetoid : Setoid (∀ i, G i) where
  r a b := ∀ᶠ i in F, a i = b i
  iseqv := {
    refl := fun _ => Filter.Eventually.of_forall fun _ => rfl
    symm := fun h => h.mono fun _ hi => hi.symm
    trans := fun h h' => by filter_upwards [h,h'] with i hi hi'; exact hi.trans hi' }

abbrev LocalUltraproduct := Quotient (localUltraSetoid F G)

abbrev localUltraMk (a : ∀ i, G i) : LocalUltraproduct F G := Quotient.mk _ a

theorem localUltraMk_eq_iff (a b : ∀ i, G i) :
    localUltraMk F G a = localUltraMk F G b ↔ ∀ᶠ i in F, a i = b i := Quotient.eq

variable (L : ∀ i, LocalGroupAlgebra (G i))

def localUltraInv : LocalUltraproduct F G → LocalUltraproduct F G :=
  Quotient.map (fun a i => (L i).inv (a i)) (by
    intro a b hab
    exact hab.mono fun i hi => congrArg (L i).inv hi)

/-- Actual componentwise multiplication, with representative independence
proved below rather than assumed through a transfer axiom. -/
def localUltraMulRel (x y z : LocalUltraproduct F G) : Prop :=
  ∃ a b c : ∀ i, G i, localUltraMk F G a = x ∧ localUltraMk F G b = y ∧
    localUltraMk F G c = z ∧ ∀ᶠ i in F, (L i).mulRel (a i) (b i) (c i)

theorem localUltraMulRel_mk_iff (a b c : ∀ i, G i) :
    localUltraMulRel F G L (localUltraMk F G a) (localUltraMk F G b) (localUltraMk F G c) ↔
      ∀ᶠ i in F, (L i).mulRel (a i) (b i) (c i) := by
  constructor
  · rintro ⟨a',b',c',ha,hb,hc,hm⟩
    have ha' := (localUltraMk_eq_iff F G a' a).1 ha
    have hb' := (localUltraMk_eq_iff F G b' b).1 hb
    have hc' := (localUltraMk_eq_iff F G c' c).1 hc
    filter_upwards [ha',hb',hc',hm] with i hai hbi hci hmi
    simpa only [hai,hbi,hci] using hmi
  · exact fun h => ⟨a,b,c,rfl,rfl,rfl,h⟩

/-- A reduced product of actual local groups is an actual local group. For an
ultrafilter this is the algebraic local-group ultraproduct. -/
def localUltraAlgebra : LocalGroupAlgebra (LocalUltraproduct F G) where
  one := localUltraMk F G fun i => (L i).one
  inv := localUltraInv F G L
  mulRel := localUltraMulRel F G L
  unique := by
    intro a b c d
    refine Quotient.inductionOn₃ a b c ?_
    intro a b c
    refine Quotient.inductionOn d ?_
    intro d hc hd
    apply Quotient.sound
    have hc' := (localUltraMulRel_mk_iff F G L a b c).1 hc
    have hd' := (localUltraMulRel_mk_iff F G L a b d).1 hd
    filter_upwards [hc',hd'] with i hi hj
    exact (L i).unique hi hj
  one_mul := by
    intro a
    refine Quotient.inductionOn a ?_
    intro a
    apply (localUltraMulRel_mk_iff F G L _ _ _).2
    exact Filter.Eventually.of_forall fun i => (L i).one_mul (a i)
  mul_one := by
    intro a
    refine Quotient.inductionOn a ?_
    intro a
    apply (localUltraMulRel_mk_iff F G L _ _ _).2
    exact Filter.Eventually.of_forall fun i => (L i).mul_one (a i)
  inv_mul := by
    intro a
    refine Quotient.inductionOn a ?_
    intro a
    apply (localUltraMulRel_mk_iff F G L _ _ _).2
    exact Filter.Eventually.of_forall fun i => (L i).inv_mul (a i)
  mul_inv := by
    intro a
    refine Quotient.inductionOn a ?_
    intro a
    apply (localUltraMulRel_mk_iff F G L _ _ _).2
    exact Filter.Eventually.of_forall fun i => (L i).mul_inv (a i)
  assoc := by
    intro a b c ab bc x y
    refine Quotient.inductionOn₃ a b c ?_
    intro a b c
    refine Quotient.inductionOn₃ ab bc x ?_
    intro ab bc x
    refine Quotient.inductionOn y ?_
    intro y hab hbc hx hy
    apply Quotient.sound
    have hab' := (localUltraMulRel_mk_iff F G L a b ab).1 hab
    have hbc' := (localUltraMulRel_mk_iff F G L b c bc).1 hbc
    have hx' := (localUltraMulRel_mk_iff F G L ab c x).1 hx
    have hy' := (localUltraMulRel_mk_iff F G L a bc y).1 hy
    filter_upwards [hab',hbc',hx',hy'] with i hi hj hk hl
    exact (L i).assoc hi hj hk hl

/-- Cancellation transfers from the component local groups, with its partial
products still checked explicitly. -/
theorem localUltraAlgebra_cancellative (hL : ∀ i, (L i).Cancellative) :
    (localUltraAlgebra F G L).Cancellative where
  left_cancel := by
    intro a b c d
    refine Quotient.inductionOn₃ a b c ?_
    intro a b c
    refine Quotient.inductionOn d ?_
    intro d hb hc
    apply Quotient.sound
    have hb' := (localUltraMulRel_mk_iff F G L a b d).1 hb
    have hc' := (localUltraMulRel_mk_iff F G L a c d).1 hc
    filter_upwards [hb',hc'] with i hi hj
    exact (hL i).left_cancel hi hj
  right_cancel := by
    intro a b c d
    refine Quotient.inductionOn₃ a b c ?_
    intro a b c
    refine Quotient.inductionOn d ?_
    intro d hb hc
    apply Quotient.sound
    have hb' := (localUltraMulRel_mk_iff F G L b a d).1 hb
    have hc' := (localUltraMulRel_mk_iff F G L c a d).1 hc
    filter_upwards [hb',hc'] with i hi hj
    exact (hL i).right_cancel hi hj
  inv_product := by
    intro a b c d
    refine Quotient.inductionOn₃ a b c ?_
    intro a b c
    refine Quotient.inductionOn d ?_
    intro d hc hd
    apply Quotient.sound
    have hc' := (localUltraMulRel_mk_iff F G L a b c).1 hc
    have hd' := (localUltraMulRel_mk_iff F G L (fun i => (L i).inv (b i)) (fun i => (L i).inv (a i)) d).1 hd
    filter_upwards [hc',hd'] with i hi hj
    exact (hL i).inv_product hi hj
end DirectedCycles
