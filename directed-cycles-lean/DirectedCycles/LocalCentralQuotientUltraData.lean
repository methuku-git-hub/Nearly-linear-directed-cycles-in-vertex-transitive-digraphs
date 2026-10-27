module

public import DirectedCycles.LocalCentralQuotientData
public import DirectedCycles.LocalEquivalenceWindowUltra
public import DirectedCycles.LocalProductDomainTransfer
public import DirectedCycles.LocalWindowUltraproduct

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace CentralQuotientData
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (P : ∀ i, Set (G i)) (D : ∀ i, (L i).CentralQuotientData (P i))

/-- The internal equivalence is exactly the relation given by actual
relative differences in the internal progression. -/
theorem ultra_relation_mk_iff (a b : ∀ i, G i)
    (ha : ∀ᶠ i in (U : Filter ι), a i ∈ (D i).small)
    (hb : ∀ᶠ i in (U : Filter ι), b i ∈ (D i).small) :
    localUltraBinaryRelation (U : Filter ι) G (fun i => (D i).equivalence.Rel)
      (localUltraMk (U : Filter ι) G a) (localUltraMk (U : Filter ι) G b) ↔
      ∃ p ∈ localUltraSet (U : Filter ι) G P,
        (localUltraAlgebra (U : Filter ι) G L).mulRel (localUltraMk (U : Filter ι) G a)
          ((localUltraAlgebra (U : Filter ι) G L).inv (localUltraMk (U : Filter ι) G b)) p := by
  classical
  rw [localUltraBinaryRelation_mk_iff]
  constructor
  · intro h
    have hex : ∀ᶠ i in (U : Filter ι), ∃ p ∈ P i, (L i).mulRel (a i) ((L i).inv (b i)) p := by
      filter_upwards [ha,hb,h] with i hai hbi hi
      exact ((D i).relation_iff ⟨a i,hai⟩ ⟨b i,hbi⟩).1 hi
    let p : ∀ i, G i := fun i => if hi : ∃ p ∈ P i, (L i).mulRel (a i) ((L i).inv (b i)) p
      then Classical.choose hi else (L i).one
    have hp : ∀ᶠ i in (U : Filter ι), p i ∈ P i ∧ (L i).mulRel (a i) ((L i).inv (b i)) (p i) := by
      filter_upwards [hex] with i hi
      dsimp only [p]
      rw [dite_eq_left hi]
      exact Classical.choose_spec hi
    exact ⟨localUltraMk (U : Filter ι) G p,(localUltraMk_mem_iff _ G P p).2 (hp.mono fun _ hi => hi.1),
      (localUltraMulRel_mk_iff _ G L a (fun i => (L i).inv (b i)) p).2 (hp.mono fun _ hi => hi.2)⟩
  · rintro ⟨p,⟨p,hp,rfl⟩,hm⟩
    have hm' := (localUltraMulRel_mk_iff _ G L a (fun i => (L i).inv (b i)) p).1 hm
    filter_upwards [ha,hb,hp,hm'] with i hai hbi hpi hmi
    exact ((D i).relation_iff ⟨a i,hai⟩ ⟨b i,hbi⟩).2 ⟨p i,hpi,hmi⟩

/-- Actual local central quotient data transfers to the internal sets,
including the exact coset relation and every small-window product domain. -/
abbrev ultraproduct : (localUltraAlgebra (U : Filter ι) G L).CentralQuotientData
    (localUltraSet (U : Filter ι) G P) where
  large := localUltraSet (U : Filter ι) G (fun i => (D i).large)
  small := localUltraSet (U : Filter ι) G (fun i => (D i).small)
  small_subset := by
    rintro x ⟨a,ha,rfl⟩
    exact (localUltraMk_mem_iff _ G _ a).2 (ha.mono fun i hi => (D i).small_subset hi)
  one_mem := localUltraWindow_one_mem _ G L _ (fun i => (D i).one_mem)
  inv_mem := localUltraWindow_inv_mem _ G L _ (fun i => (D i).inv_mem)
  domain := (localUltra_allProductsDefined_iff U G L _ 3).2
    (Filter.Eventually.of_forall fun i => (D i).domain)
  cube_subset := by
    intro x hx
    obtain ⟨a,rfl⟩ := Quotient.exists_rep x
    have hh := (localUltra_wordPower_mk_iff (U : Filter ι) G L _ a 3).1 hx
    exact (localUltraMk_mem_iff _ G _ a).2 (hh.mono fun i hi => (D i).cube_subset hi)
  equivalence := EquivalenceWindow.ultraproduct (U : Filter ι) G L _ (fun i => (D i).equivalence)
  relation_iff := by
    rintro ⟨a,ha⟩ ⟨b,hb⟩
    change localUltraBinaryRelation (U : Filter ι) G (fun i => (D i).equivalence.Rel) a b ↔ _
    revert ha hb
    refine Quotient.inductionOn₂ a b ?_
    intro a b ha hb
    exact ultra_relation_mk_iff U G L P D a b
      ((localUltraMk_mem_iff _ G _ a).1 ha) ((localUltraMk_mem_iff _ G _ b).1 hb)
end CentralQuotientData
end LocalGroupAlgebra
end DirectedCycles
