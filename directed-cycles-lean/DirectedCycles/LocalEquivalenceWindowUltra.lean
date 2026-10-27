module

public import DirectedCycles.LocalEquivalenceWindow
public import DirectedCycles.LocalUltraBinaryRelation
public import DirectedCycles.LocalInternalSetLogic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace EquivalenceWindow
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (S : ∀ i, Set (G i)) (C : ∀ i, (L i).EquivalenceWindow (S i))

/-- Component equivalences on actual large windows give an equivalence on
the internal large window. Every domain and relation premise transfers with
its representatives; no unrestricted transfer principle is assumed. -/
def ultraproduct : (localUltraAlgebra F G L).EquivalenceWindow (localUltraSet F G S) where
  Rel := localUltraBinaryRelation F G (fun i => (C i).Rel)
  refl := by
    rintro a ⟨a,ha,rfl⟩
    apply (localUltraBinaryRelation_mk_iff F G _ a a).2
    exact ha.mono fun i hi => (C i).refl (a i) hi
  symm := by
    rintro a ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩ h
    have hh := (localUltraBinaryRelation_mk_iff F G _ a b).1 h
    apply (localUltraBinaryRelation_mk_iff F G _ b a).2
    filter_upwards [ha,hb,hh] with i hai hbi hi
    exact (C i).symm (a i) hai (b i) hbi hi
  trans := by
    rintro a ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩ c ⟨c,hc,rfl⟩ h h'
    have hh := (localUltraBinaryRelation_mk_iff F G _ a b).1 h
    have hh' := (localUltraBinaryRelation_mk_iff F G _ b c).1 h'
    apply (localUltraBinaryRelation_mk_iff F G _ a c).2
    filter_upwards [ha,hb,hc,hh,hh'] with i hai hbi hci hi hi'
    exact (C i).trans (a i) hai (b i) hbi (c i) hci hi hi'
  inv_rel := by
    rintro a ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩ h
    have hh := (localUltraBinaryRelation_mk_iff F G _ a b).1 h
    apply (localUltraBinaryRelation_mk_iff F G _ (fun i => (L i).inv (a i)) (fun i => (L i).inv (b i))).2
    filter_upwards [ha,hb,hh] with i hai hbi hi
    exact (C i).inv_rel (a i) hai (b i) hbi hi
  mul_rel := by
    rintro a ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩ c ⟨c,hc,rfl⟩ a' ⟨a',ha',rfl⟩ b' ⟨b',hb',rfl⟩ c' ⟨c',hc',rfl⟩ hm hm' h h'
    have hm0 := (localUltraMulRel_mk_iff F G L a b c).1 hm
    have hm1 := (localUltraMulRel_mk_iff F G L a' b' c').1 hm'
    have hh := (localUltraBinaryRelation_mk_iff F G _ a a').1 h
    have hh' := (localUltraBinaryRelation_mk_iff F G _ b b').1 h'
    apply (localUltraBinaryRelation_mk_iff F G _ c c').2
    filter_upwards [ha,hb,hc,ha',hb',hc',hm0,hm1,hh,hh'] with i hai hbi hci hai' hbi' hci' hmi hmi' hi hi'
    exact (C i).mul_rel (a i) hai (b i) hbi (c i) hci (a' i) hai' (b' i) hbi' (c' i) hci' hmi hmi' hi hi'
end EquivalenceWindow
end LocalGroupAlgebra
end DirectedCycles
