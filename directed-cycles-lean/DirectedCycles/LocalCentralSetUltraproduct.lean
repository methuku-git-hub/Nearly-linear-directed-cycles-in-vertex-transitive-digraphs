module

public import DirectedCycles.LocalCentralEquivalence
public import DirectedCycles.LocalGroupUltraproduct
public import DirectedCycles.LocalInternalSetLogic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- Central local closure transfers to the actual internal sets, including
existence of both products in every claimed commutation relation. -/
theorem localUltra_centralLocalSet (P V S : ∀ i, Set (G i))
    (hP : ∀ i, (L i).CentralLocalSet (P i) (V i) (S i)) :
    (localUltraAlgebra (U : Filter ι) G L).CentralLocalSet
      (localUltraSet (U : Filter ι) G P) (localUltraSet (U : Filter ι) G V)
      (localUltraSet (U : Filter ι) G S) := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · exact (localUltraMk_mem_iff _ G P (fun i => (L i).one)).2
      (Filter.Eventually.of_forall fun i => (hP i).one_mem)
  · rintro _ ⟨p,hp,rfl⟩
    exact (localUltraMk_mem_iff _ G P (fun i => (L i).inv (p i))).2
      (hp.mono fun i hi => (hP i).inv_mem (p i) hi)
  · rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ _ ⟨z,hz,rfl⟩ hm
    have hm' := (localUltraMulRel_mk_iff _ G L p q z).1 hm
    apply (localUltraMk_mem_iff _ G P z).2
    filter_upwards [hp,hq,hz,hm'] with i hpi hqi hzi hmi
    exact (hP i).mul_mem (p i) hpi (q i) hqi (z i) hzi hmi
  · rintro _ ⟨p,hp,rfl⟩ _ ⟨x,hx,rfl⟩
    have hc : ∀ᶠ i in (U : Filter ι), (L i).Commute (p i) (x i) := by
      filter_upwards [hp,hx] with i hpi hxi
      exact (hP i).central (p i) hpi (x i) hxi
    let z : ∀ i, G i := fun i => if hi : (L i).Commute (p i) (x i)
      then Classical.choose hi else (L i).one
    have hz : ∀ᶠ i in (U : Filter ι),
        (L i).mulRel (p i) (x i) (z i) ∧ (L i).mulRel (x i) (p i) (z i) := by
      filter_upwards [hc] with i hi
      dsimp only [z]
      rw [dite_eq_left hi]
      exact Classical.choose_spec hi
    exact ⟨localUltraMk (U : Filter ι) G z,
      (localUltraMulRel_mk_iff _ G L p x z).2 (hz.mono fun _ hi => hi.1),
      (localUltraMulRel_mk_iff _ G L x p z).2 (hz.mono fun _ hi => hi.2)⟩
end DirectedCycles
