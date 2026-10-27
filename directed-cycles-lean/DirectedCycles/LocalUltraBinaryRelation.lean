module

public import DirectedCycles.LocalGroupUltraproduct

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (R : ∀ i, G i → G i → Prop)

/-- The actual reduced-product relation, independent of representatives. -/
def localUltraBinaryRelation (x y : LocalUltraproduct F G) : Prop :=
  ∃ a b : ∀ i, G i, localUltraMk F G a = x ∧ localUltraMk F G b = y ∧ ∀ᶠ i in F, R i (a i) (b i)

theorem localUltraBinaryRelation_mk_iff (a b : ∀ i, G i) :
    localUltraBinaryRelation F G R (localUltraMk F G a) (localUltraMk F G b) ↔
      ∀ᶠ i in F, R i (a i) (b i) := by
  constructor
  · rintro ⟨a',b',ha,hb,hR⟩
    have ha' := (localUltraMk_eq_iff F G a' a).1 ha
    have hb' := (localUltraMk_eq_iff F G b' b).1 hb
    filter_upwards [ha',hb',hR] with i hai hbi hRi
    simpa only [hai,hbi] using hRi
  · exact fun h => ⟨a,b,rfl,rfl,h⟩
end DirectedCycles
