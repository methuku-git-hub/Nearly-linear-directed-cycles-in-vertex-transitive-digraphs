module

public import DirectedCycles.LocalQuotientUltraproduct

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalQuotientData
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (D : ∀ i, LocalQuotientData (G i))

/-- The quotient-ultraproduct equivalence preserves and reflects the actual
partial multiplication relation, not just the underlying coset sets. -/
theorem quotientUltraEquiv_mul_iff (x y z : LocalUltraproduct F (fun i => (D i).Carrier)) :
    (localUltraAlgebra F (fun i => (D i).Carrier) (fun i => (D i).algebra)).mulRel x y z ↔
      (ultraproduct F G D).algebra.mulRel (quotientUltraEquiv F G D x)
        (quotientUltraEquiv F G D y) (quotientUltraEquiv F G D z) := by
  classical
  refine Quotient.inductionOn₃ x y z ?_
  intro x y z
  constructor
  · intro h
    have hc := (localUltraMulRel_mk_iff F _ (fun i => (D i).algebra) x y z).1 h
    have hchoose : ∀ i, ∃ a b c : (D i).W, (D i).algebra.mulRel (x i) (y i) (z i) →
        (D i).project a = x i ∧ (D i).project b = y i ∧ (D i).project c = z i ∧ a.val*b.val = c.val := by
      intro i
      by_cases hi : (D i).algebra.mulRel (x i) (y i) (z i)
      · obtain ⟨a,b,c,ha,hb,hc,hab⟩ := hi
        exact ⟨a,b,c,fun _ => ⟨ha,hb,hc,hab⟩⟩
      · exact ⟨⟨1,(D i).one_mem⟩,⟨1,(D i).one_mem⟩,⟨1,(D i).one_mem⟩,fun hh => (hi hh).elim⟩
    choose a b c habc using hchoose
    have hh : ∀ᶠ i in F, (D i).project (a i) = x i ∧ (D i).project (b i) = y i ∧
        (D i).project (c i) = z i ∧ (a i).val*(b i).val = (c i).val := hc.mono fun i hi => habc i hi
    let aU := localUltraMk F (fun i => (D i).W) a
    let bU := localUltraMk F (fun i => (D i).W) b
    let cU := localUltraMk F (fun i => (D i).W) c
    have ha : componentProjection F G D aU = localUltraMk F _ x :=
      (localUltraMk_eq_iff F _ _ _).2 (hh.mono fun _ hi => hi.1)
    have hb : componentProjection F G D bU = localUltraMk F _ y :=
      (localUltraMk_eq_iff F _ _ _).2 (hh.mono fun _ hi => hi.2.1)
    have hc : componentProjection F G D cU = localUltraMk F _ z :=
      (localUltraMk_eq_iff F _ _ _).2 (hh.mono fun _ hi => hi.2.2.1)
    refine ⟨ultraWindowMap F G (fun i => (D i).W) aU,
      ultraWindowMap F G (fun i => (D i).W) bU,
      ultraWindowMap F G (fun i => (D i).W) cU,?_,?_,?_,?_⟩
    · exact (quotientUltraEquiv_projection F G D aU).symm.trans (congrArg (quotientUltraEquiv F G D) ha)
    · exact (quotientUltraEquiv_projection F G D bU).symm.trans (congrArg (quotientUltraEquiv F G D) hb)
    · exact (quotientUltraEquiv_projection F G D cU).symm.trans (congrArg (quotientUltraEquiv F G D) hc)
    · change ultraMk F G (fun i => (a i).val)*ultraMk F G (fun i => (b i).val) =
        ultraMk F G (fun i => (c i).val)
      rw [← map_mul]
      exact (ultraMk_eq_iff F G _ _).2 (hh.mono fun _ hi => hi.2.2.2)
  · rintro ⟨a,b,c,ha,hb,hc,hab⟩
    obtain ⟨aU,rfl⟩ := ultraWindowMap_surjective F G (fun i => (D i).W) (fun i => (D i).one_mem) a
    obtain ⟨bU,rfl⟩ := ultraWindowMap_surjective F G (fun i => (D i).W) (fun i => (D i).one_mem) b
    obtain ⟨cU,rfl⟩ := ultraWindowMap_surjective F G (fun i => (D i).W) (fun i => (D i).one_mem) c
    obtain ⟨a,rfl⟩ := Quotient.exists_rep aU
    obtain ⟨b,rfl⟩ := Quotient.exists_rep bU
    obtain ⟨c,rfl⟩ := Quotient.exists_rep cU
    have ha' : componentProjection F G D (localUltraMk F _ a) = localUltraMk F _ x := by
      apply (quotientUltraEquiv F G D).injective
      exact (quotientUltraEquiv_projection F G D _).trans ha
    have hb' : componentProjection F G D (localUltraMk F _ b) = localUltraMk F _ y := by
      apply (quotientUltraEquiv F G D).injective
      exact (quotientUltraEquiv_projection F G D _).trans hb
    have hc' : componentProjection F G D (localUltraMk F _ c) = localUltraMk F _ z := by
      apply (quotientUltraEquiv F G D).injective
      exact (quotientUltraEquiv_projection F G D _).trans hc
    have haE := (localUltraMk_eq_iff F _ _ _).1 ha'
    have hbE := (localUltraMk_eq_iff F _ _ _).1 hb'
    have hcE := (localUltraMk_eq_iff F _ _ _).1 hc'
    change ultraMk F G (fun i => (a i).val)*ultraMk F G (fun i => (b i).val) =
      ultraMk F G (fun i => (c i).val) at hab
    rw [← map_mul] at hab
    have habE := (ultraMk_eq_iff F G _ _).1 hab
    apply (localUltraMulRel_mk_iff F _ (fun i => (D i).algebra) x y z).2
    filter_upwards [haE,hbE,hcE,habE] with i hai hbi hci habi
    exact ⟨a i,b i,c i,hai,hbi,hci,habi⟩
end LocalQuotientData
end DirectedCycles
