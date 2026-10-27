module

public import DirectedCycles.LocalCentralQuotientUltraEquiv

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace CentralQuotientData
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (P : ∀ i, Set (G i)) (D : ∀ i, (L i).CentralQuotientData (P i))

/-- The quotient-ultraproduct equivalence preserves and reflects the actual
partial multiplication relation, not just the underlying coset sets. -/
theorem quotientUltraEquiv_mul_iff (x y z : LocalUltraproduct (U : Filter ι) (fun i => (D i).Carrier)) :
    (localUltraAlgebra (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).algebra)).mulRel x y z ↔
      (ultraproduct U G L P D).algebra.mulRel (quotientUltraEquiv U G L P D x)
        (quotientUltraEquiv U G L P D y) (quotientUltraEquiv U G L P D z) := by
  classical
  refine Quotient.inductionOn₃ x y z ?_
  intro x y z
  constructor
  · intro h
    have hc := (localUltraMulRel_mk_iff (U : Filter ι) _ (fun i => (D i).algebra) x y z).1 h
    have hchoose : ∀ i, ∃ a b c : (D i).small, (D i).algebra.mulRel (x i) (y i) (z i) →
        (D i).project a = x i ∧ (D i).project b = y i ∧ (D i).project c = z i ∧ (L i).mulRel a.val b.val c.val := by
      intro i
      by_cases hi : (D i).algebra.mulRel (x i) (y i) (z i)
      · obtain ⟨a,b,c,ha,hb,hc,hab⟩ := hi
        exact ⟨a,b,c,fun _ => ⟨ha,hb,hc,hab⟩⟩
      · exact ⟨⟨(L i).one,(D i).one_mem⟩,⟨(L i).one,(D i).one_mem⟩,⟨(L i).one,(D i).one_mem⟩,fun hh => (hi hh).elim⟩
    choose a b c habc using hchoose
    have hh : ∀ᶠ i in (U : Filter ι), (D i).project (a i) = x i ∧ (D i).project (b i) = y i ∧
        (D i).project (c i) = z i ∧ (L i).mulRel (a i).val (b i).val (c i).val := hc.mono fun i hi => habc i hi
    let aU := localUltraMk (U : Filter ι) (fun i => (D i).small) a
    let bU := localUltraMk (U : Filter ι) (fun i => (D i).small) b
    let cU := localUltraMk (U : Filter ι) (fun i => (D i).small) c
    have ha : componentProjection U G L P D aU = localUltraMk (U : Filter ι) _ x :=
      (localUltraMk_eq_iff (U : Filter ι) _ _ _).2 (hh.mono fun _ hi => hi.1)
    have hb : componentProjection U G L P D bU = localUltraMk (U : Filter ι) _ y :=
      (localUltraMk_eq_iff (U : Filter ι) _ _ _).2 (hh.mono fun _ hi => hi.2.1)
    have hc : componentProjection U G L P D cU = localUltraMk (U : Filter ι) _ z :=
      (localUltraMk_eq_iff (U : Filter ι) _ _ _).2 (hh.mono fun _ hi => hi.2.2.1)
    refine ⟨localUltraWindowMap (U : Filter ι) G (fun i => (D i).small) aU,
      localUltraWindowMap (U : Filter ι) G (fun i => (D i).small) bU,
      localUltraWindowMap (U : Filter ι) G (fun i => (D i).small) cU,?_,?_,?_,?_⟩
    · exact (quotientUltraEquiv_projection U G L P D aU).symm.trans (congrArg (quotientUltraEquiv U G L P D) ha)
    · exact (quotientUltraEquiv_projection U G L P D bU).symm.trans (congrArg (quotientUltraEquiv U G L P D) hb)
    · exact (quotientUltraEquiv_projection U G L P D cU).symm.trans (congrArg (quotientUltraEquiv U G L P D) hc)
    · change (localUltraAlgebra (U : Filter ι) G L).mulRel
        (localUltraMk (U : Filter ι) G (fun i => (a i).val))
        (localUltraMk (U : Filter ι) G (fun i => (b i).val))
        (localUltraMk (U : Filter ι) G (fun i => (c i).val))
      exact (localUltraMulRel_mk_iff (U : Filter ι) G L _ _ _).2 (hh.mono fun _ hi => hi.2.2.2)
  · rintro ⟨a,b,c,ha,hb,hc,hab⟩
    obtain ⟨aU,rfl⟩ := localUltraWindowMap_surjective (U : Filter ι) G L (fun i => (D i).small) (fun i => (D i).one_mem) a
    obtain ⟨bU,rfl⟩ := localUltraWindowMap_surjective (U : Filter ι) G L (fun i => (D i).small) (fun i => (D i).one_mem) b
    obtain ⟨cU,rfl⟩ := localUltraWindowMap_surjective (U : Filter ι) G L (fun i => (D i).small) (fun i => (D i).one_mem) c
    obtain ⟨a,rfl⟩ := Quotient.exists_rep aU
    obtain ⟨b,rfl⟩ := Quotient.exists_rep bU
    obtain ⟨c,rfl⟩ := Quotient.exists_rep cU
    have ha' : componentProjection U G L P D (localUltraMk (U : Filter ι) _ a) = localUltraMk (U : Filter ι) _ x := by
      apply (quotientUltraEquiv U G L P D).injective
      exact (quotientUltraEquiv_projection U G L P D _).trans ha
    have hb' : componentProjection U G L P D (localUltraMk (U : Filter ι) _ b) = localUltraMk (U : Filter ι) _ y := by
      apply (quotientUltraEquiv U G L P D).injective
      exact (quotientUltraEquiv_projection U G L P D _).trans hb
    have hc' : componentProjection U G L P D (localUltraMk (U : Filter ι) _ c) = localUltraMk (U : Filter ι) _ z := by
      apply (quotientUltraEquiv U G L P D).injective
      exact (quotientUltraEquiv_projection U G L P D _).trans hc
    have haE := (localUltraMk_eq_iff (U : Filter ι) _ _ _).1 ha'
    have hbE := (localUltraMk_eq_iff (U : Filter ι) _ _ _).1 hb'
    have hcE := (localUltraMk_eq_iff (U : Filter ι) _ _ _).1 hc'
    change (localUltraAlgebra (U : Filter ι) G L).mulRel
      (localUltraMk (U : Filter ι) G (fun i => (a i).val))
      (localUltraMk (U : Filter ι) G (fun i => (b i).val))
      (localUltraMk (U : Filter ι) G (fun i => (c i).val)) at hab
    have habE := (localUltraMulRel_mk_iff (U : Filter ι) G L _ _ _).1 hab
    apply (localUltraMulRel_mk_iff (U : Filter ι) _ (fun i => (D i).algebra) x y z).2
    filter_upwards [haE,hbE,hcE,habE] with i hai hbi hci habi
    exact ⟨a i,b i,c i,hai,hbi,hci,habi⟩
end CentralQuotientData
end LocalGroupAlgebra
end DirectedCycles
