import DirectedCycles.LocalGlobalSubgroup
import DirectedCycles.LocalInternalSetLogic

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

theorem localUltra_exists_product_in_iff (a b : ∀ i, G i) (H : ∀ i, Set (G i)) :
    (∃ z ∈ localUltraSet F G H,
      (localUltraAlgebra F G L).mulRel (localUltraMk F G a) (localUltraMk F G b) z) ↔
      ∀ᶠ i in F, ∃ z ∈ H i, (L i).mulRel (a i) (b i) z := by
  classical
  constructor
  · rintro ⟨z,⟨c,hc,rfl⟩,hm⟩
    have hm' := (localUltraMulRel_mk_iff F G L a b c).1 hm
    filter_upwards [hc,hm'] with i hi hmi
    exact ⟨c i,hi,hmi⟩
  · intro h
    let c : ∀ i, G i := fun i => if hi : ∃ z ∈ H i, (L i).mulRel (a i) (b i) z
      then Classical.choose hi else (L i).one
    have hc : ∀ᶠ i in F, c i ∈ H i ∧ (L i).mulRel (a i) (b i) (c i) := by
      filter_upwards [h] with i hi
      dsimp only [c]
      rw [dite_eq_left hi]
      exact Classical.choose_spec hi
    exact ⟨localUltraMk F G c,(localUltraMk_mem_iff F G H c).2 (hc.mono fun _ hi => hi.1),
      (localUltraMulRel_mk_iff F G L a b c).2 (hc.mono fun _ hi => hi.2)⟩

/-- Actual component global subgroups give a global subgroup of the local
ultraproduct, including total multiplication on the internal subset. -/
theorem localUltraSet_isGlobalSubgroup (H : ∀ i, Set (G i))
    (hH : ∀ᶠ i in F, (L i).IsGlobalSubgroup (H i)) :
    (localUltraAlgebra F G L).IsGlobalSubgroup (localUltraSet F G H) where
  one_mem := (localUltraMk_mem_iff F G H (fun i => (L i).one)).2
    (hH.mono fun _ hi => hi.one_mem)
  inv_mem := by
    rintro x ⟨a,ha,rfl⟩
    apply (localUltraMk_mem_iff F G H (fun i => (L i).inv (a i))).2
    filter_upwards [hH,ha] with i hi hai
    exact hi.inv_mem (a i) hai
  mul_total := by
    rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩
    apply (localUltra_exists_product_in_iff F G L a b H).2
    filter_upwards [hH,ha,hb] with i hi hai hbi
    exact hi.mul_total (a i) hai (b i) hbi

/-- Conversely, if the actual internal subset is a global subgroup, its
components are global subgroups almost everywhere. The universal part is
proved using internal subset transfer on the component pair spaces. -/
theorem localUltraSet_isGlobalSubgroup_iff (u : Ultrafilter ι) (H : ∀ i, Set (G i)) :
    (localUltraAlgebra (u : Filter ι) G L).IsGlobalSubgroup (localUltraSet (u : Filter ι) G H) ↔
      ∀ᶠ i in (u : Filter ι), (L i).IsGlobalSubgroup (H i) := by
  constructor
  · intro hH
    have h1 : ∀ᶠ i in (u : Filter ι), (L i).one ∈ H i :=
      (localUltraMk_mem_iff _ G H (fun i => (L i).one)).1 hH.one_mem
    have hinv : localUltraSet (u : Filter ι) G H ⊆
        localUltraSet (u : Filter ι) G (fun i => {x | (L i).inv x ∈ H i}) := by
      rintro x ⟨a,ha,rfl⟩
      have hx := hH.inv_mem (localUltraMk (u : Filter ι) G a) ⟨a,ha,rfl⟩
      exact (localUltraMk_mem_iff _ G _ a).2
        ((localUltraMk_mem_iff _ G H (fun i => (L i).inv (a i))).1 hx)
    have hi := (localUltraSet_subset_iff_eventually u G (fun i => (L i).one) H _).1 hinv
    let GP := fun i => G i × G i
    let HP := fun i => H i ×ˢ H i
    let MP := fun i => {p : GP i | ∃ z ∈ H i, (L i).mulRel p.1 p.2 z}
    have hmul : localUltraSet (u : Filter ι) GP HP ⊆ localUltraSet (u : Filter ι) GP MP := by
      rintro x ⟨p,hp,rfl⟩
      have ha : localUltraMk (u : Filter ι) G (fun i => (p i).1) ∈ localUltraSet (u : Filter ι) G H :=
        (localUltraMk_mem_iff _ G H _).2 (hp.mono fun _ h => h.1)
      have hb : localUltraMk (u : Filter ι) G (fun i => (p i).2) ∈ localUltraSet (u : Filter ι) G H :=
        (localUltraMk_mem_iff _ G H _).2 (hp.mono fun _ h => h.2)
      have hm := (localUltra_exists_product_in_iff (u : Filter ι) G L
        (fun i => (p i).1) (fun i => (p i).2) H).1 (hH.mul_total _ ha _ hb)
      exact (localUltraMk_mem_iff _ GP MP p).2 hm
    have hm := (localUltraSet_subset_iff_eventually u GP (fun i => ((L i).one,(L i).one)) HP MP).1 hmul
    filter_upwards [h1,hi,hm] with i h1i hii hmi
    exact ⟨h1i,fun x hx => hii hx,fun x hx y hy => hmi (a := (x,y)) ⟨hx,hy⟩⟩
  · exact localUltraSet_isGlobalSubgroup (u : Filter ι) G L H

/-- NSS for an internal local approximate set excludes actual global subgroups
that are internal. Arbitrary external subgroups are not ruled out. -/
def LocalInternalNSS (u : Ultrafilter ι) (A : ∀ i, Set (G i)) : Prop :=
  ∀ H : ∀ i, Set (G i),
    (localUltraAlgebra (u : Filter ι) G L).IsGlobalSubgroup (localUltraSet (u : Filter ι) G H) →
    localUltraSet (u : Filter ι) G H ⊆ localUltraSet (u : Filter ι) G A →
    localUltraSet (u : Filter ι) G H ⊆ {(localUltraAlgebra (u : Filter ι) G L).one}

theorem local_internal_nss_of_components (u : Ultrafilter ι) (A : ∀ i, Set (G i))
    (hNSS : ∀ᶠ i in (u : Filter ι), (L i).IsNSS (A i)) : LocalInternalNSS G L u A := by
  intro H hH hHA
  have hh := (localUltraSet_isGlobalSubgroup_iff G L u H).1 hH
  have hsub := (localUltraSet_subset_iff_eventually u G (fun i => (L i).one) H A).1 hHA
  rintro x ⟨a,ha,rfl⟩
  change localUltraMk (u : Filter ι) G a = localUltraMk (u : Filter ι) G (fun i => (L i).one)
  apply (localUltraMk_eq_iff _ G _ _).2
  filter_upwards [hNSS,hh,hsub,ha] with i hi hhi hsi hai
  exact hi (H i) hhi hsi hai
end DirectedCycles
