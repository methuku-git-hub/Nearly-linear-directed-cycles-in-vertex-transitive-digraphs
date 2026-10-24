import DirectedCycles.LocalGroupCongruence
import DirectedCycles.LocalUltraproductMaps
import DirectedCycles.LocalInternalSetLogic

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupCongruence
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (C : ∀ i, LocalGroupCongruence (L i))

abbrev ultraProjection : LocalUltraproduct F G → LocalUltraproduct F (fun i => (C i).Carrier) :=
  localUltraMap F G (fun i => (C i).Carrier) (fun i => (C i).project)

def ultraProjectionHom : LocalGroupHom (localUltraAlgebra F G L)
    (localUltraAlgebra F (fun i => (C i).Carrier) (fun i => (C i).algebra)) :=
  localUltraHom F G _ L _ (fun i => (C i).projectionHom)

theorem ultraProjection_surjective : Function.Surjective (ultraProjection F G L C) :=
  localUltraMap_surjective F G _ _ (fun _ => Quotient.mk_surjective)

/-- The kernel relation of the actual component quotient map transports
all local product domains. The component domain-transport witnesses are
chosen only where the required relations hold. -/
def ultraproduct : LocalGroupCongruence (localUltraAlgebra F G L) where
  toSetoid := Setoid.ker (ultraProjection F G L C)
  inv_rel := by
    intro a b h
    change (ultraProjectionHom F G L C).toFun ((localUltraAlgebra F G L).inv a) =
      (ultraProjectionHom F G L C).toFun ((localUltraAlgebra F G L).inv b)
    rw [(ultraProjectionHom F G L C).map_inv,(ultraProjectionHom F G L C).map_inv]
    exact congrArg (localUltraAlgebra F (fun i => (C i).Carrier) (fun i => (C i).algebra)).inv h
  mul_lift := by
    classical
    intro a b c a' b' hm ha hb
    obtain ⟨a,rfl⟩ := Quotient.exists_rep a
    obtain ⟨b,rfl⟩ := Quotient.exists_rep b
    obtain ⟨c,rfl⟩ := Quotient.exists_rep c
    obtain ⟨a',rfl⟩ := Quotient.exists_rep a'
    obtain ⟨b',rfl⟩ := Quotient.exists_rep b'
    have hm' := (localUltraMulRel_mk_iff F G L a b c).1 hm
    have ha' : ∀ᶠ i in F, (C i).project (a i) = (C i).project (a' i) :=
      (localUltraMk_eq_iff F _ _ _).1 ha
    have hb' : ∀ᶠ i in F, (C i).project (b i) = (C i).project (b' i) :=
      (localUltraMk_eq_iff F _ _ _).1 hb
    have hex : ∀ᶠ i in F, ∃ d, (L i).mulRel (a' i) (b' i) d ∧ (C i).project (c i) = (C i).project d := by
      filter_upwards [hm',ha',hb'] with i hmi hai hbi
      obtain ⟨d,hd,he⟩ := (C i).mul_lift hmi (Quotient.exact hai) (Quotient.exact hbi)
      exact ⟨d,hd,Quotient.sound he⟩
    let d : ∀ i, G i := fun i => if hi : ∃ d, (L i).mulRel (a' i) (b' i) d ∧ (C i).project (c i) = (C i).project d
      then Classical.choose hi else (L i).one
    have hde : ∀ᶠ i in F, (L i).mulRel (a' i) (b' i) (d i) ∧
        (C i).project (c i) = (C i).project (d i) := by
      filter_upwards [hex] with i hi
      dsimp only [d]
      rw [dite_eq_left hi]
      exact Classical.choose_spec hi
    exact ⟨localUltraMk F G d,(localUltraMulRel_mk_iff F G L a' b' d).2 (hde.mono fun _ hi => hi.1),
      (localUltraMk_eq_iff F _ _ _).2 (hde.mono fun _ hi => hi.2)⟩

/-- Quotienting the actual local ultraproduct by the internal component
congruence gives exactly the ultraproduct of the actual component quotients. -/
noncomputable def quotientUltraEquiv : (ultraproduct F G L C).Carrier ≃
    LocalUltraproduct F (fun i => (C i).Carrier) :=
  Equiv.ofBijective (Quotient.lift (ultraProjection F G L C) (fun _ _ h => h)) (by
    constructor
    · intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro x y he
      exact Quotient.sound he
    · intro z
      obtain ⟨x,hx⟩ := ultraProjection_surjective F G L C z
      exact ⟨(ultraproduct F G L C).project x,hx⟩)

theorem quotientUltraEquiv_project (a : LocalUltraproduct F G) :
    quotientUltraEquiv F G L C ((ultraproduct F G L C).project a) = ultraProjection F G L C a := rfl

/-- The equivalence preserves and reflects the exact multiplication relation;
undefined products remain undefined. -/
theorem quotientUltraEquiv_mul_iff (x y z : (ultraproduct F G L C).Carrier) :
    (ultraproduct F G L C).algebra.mulRel x y z ↔
      (localUltraAlgebra F (fun i => (C i).Carrier) (fun i => (C i).algebra)).mulRel
        (quotientUltraEquiv F G L C x) (quotientUltraEquiv F G L C y) (quotientUltraEquiv F G L C z) := by
  constructor
  · rintro ⟨a,b,c,rfl,rfl,rfl,hm⟩
    exact (ultraProjectionHom F G L C).map_mul hm
  · intro hm
    obtain ⟨a,rfl⟩ := Quotient.exists_rep x
    obtain ⟨b,rfl⟩ := Quotient.exists_rep y
    obtain ⟨c,rfl⟩ := Quotient.exists_rep z
    obtain ⟨a,rfl⟩ := Quotient.exists_rep a
    obtain ⟨b,rfl⟩ := Quotient.exists_rep b
    obtain ⟨c,rfl⟩ := Quotient.exists_rep c
    have hm' := (localUltraMulRel_mk_iff F (fun i => (C i).Carrier) (fun i => (C i).algebra)
      (fun i => (C i).project (a i)) (fun i => (C i).project (b i)) (fun i => (C i).project (c i))).1 hm
    classical
    let d : ∀ i, G i := fun i => if hi : (C i).algebra.mulRel ((C i).project (a i))
        ((C i).project (b i)) ((C i).project (c i))
      then Classical.choose ((C i).lift_mul hi) else (L i).one
    have hde : ∀ᶠ i in F, (C i).project (d i) = (C i).project (c i) ∧ (L i).mulRel (a i) (b i) (d i) := by
      filter_upwards [hm'] with i hi
      dsimp only [d]
      rw [dite_eq_left hi]
      exact Classical.choose_spec ((C i).lift_mul hi)
    refine ⟨localUltraMk F G a,localUltraMk F G b,localUltraMk F G d,rfl,rfl,?_,
      (localUltraMulRel_mk_iff F G L a b d).2 (hde.mono fun _ hi => hi.2)⟩
    apply Quotient.sound
    exact (localUltraMk_eq_iff F _ _ _).2 (hde.mono fun _ hi => hi.1)
end LocalGroupCongruence
end DirectedCycles
