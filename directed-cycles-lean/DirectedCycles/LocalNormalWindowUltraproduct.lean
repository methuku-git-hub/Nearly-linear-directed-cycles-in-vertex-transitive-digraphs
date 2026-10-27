module

public import DirectedCycles.LocalWindowNSS
public import DirectedCycles.LocalInternalSubgroups
public import DirectedCycles.LocalWindowUltraproduct
public import DirectedCycles.LocalPowerTrappingTransfer

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace NormalSubgroupWindow
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (H S : ∀ i, Set (G i)) (W : ∀ i, (L i).NormalSubgroupWindow (H i) (S i))

include W in
/-- An internal family of saturated normal subgroup windows gives an actual
normal subgroup window in the local ultraproduct. Normality and saturation
include the required product witnesses. -/
theorem ultraproduct : (localUltraAlgebra (U : Filter ι) G L).NormalSubgroupWindow
    (localUltraSet (U : Filter ι) G H) (localUltraSet (U : Filter ι) G S) where
  subgroup := localUltraSet_isGlobalSubgroup (U : Filter ι) G L H
    (Filter.Eventually.of_forall fun i => (W i).subgroup)
  subset := (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) H S).2
    (Filter.Eventually.of_forall fun i => (W i).subset)
  inv_mem := localUltraWindow_inv_mem (U : Filter ι) G L S (fun i => (W i).inv_mem)
  binary := by
    rintro a ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩
    apply (localUltra_defined_mk_iff (U : Filter ι) G L a b).2
    filter_upwards [ha,hb] with i hai hbi
    exact (W i).binary (a i) hai (b i) hbi
  saturated := by
    rintro h ⟨h,hh,rfl⟩ s ⟨s,hs,rfl⟩
    apply (localUltra_exists_product_in_iff (U : Filter ι) G L h s S).2
    filter_upwards [hh,hs] with i hhi hsi
    exact (W i).saturated (h i) hhi (s i) hsi
  normal := by
    classical
    rintro s ⟨s,hs,rfl⟩ h ⟨h,hh,rfl⟩
    have hex : ∀ᶠ i in (U : Filter ι), ∃ k ∈ H i, ∃ t,
        (L i).mulRel (s i) (h i) t ∧ (L i).mulRel k (s i) t := by
      filter_upwards [hs,hh] with i hsi hhi
      exact (W i).normal (s i) hsi (h i) hhi
    let k : ∀ i, G i := fun i => if hi : ∃ k ∈ H i, ∃ t,
        (L i).mulRel (s i) (h i) t ∧ (L i).mulRel k (s i) t
      then Classical.choose hi else (L i).one
    have hk : ∀ᶠ i in (U : Filter ι), k i ∈ H i ∧ ∃ t,
        (L i).mulRel (s i) (h i) t ∧ (L i).mulRel (k i) (s i) t := by
      filter_upwards [hex] with i hi
      dsimp only [k]
      rw [dite_eq_left hi]
      exact Classical.choose_spec hi
    let t : ∀ i, G i := fun i => if hi : ∃ t,
        (L i).mulRel (s i) (h i) t ∧ (L i).mulRel (k i) (s i) t
      then Classical.choose hi else (L i).one
    have ht : ∀ᶠ i in (U : Filter ι),
        (L i).mulRel (s i) (h i) (t i) ∧ (L i).mulRel (k i) (s i) (t i) := by
      filter_upwards [hk] with i hi
      dsimp only [t]
      rw [dite_eq_left hi.2]
      exact Classical.choose_spec hi.2
    exact ⟨localUltraMk (U : Filter ι) G k,(localUltraMk_mem_iff _ G H k).2 (hk.mono fun _ hi => hi.1),
      localUltraMk (U : Filter ι) G t,(localUltraMulRel_mk_iff _ G L s h t).2 (ht.mono fun _ hi => hi.1),
      (localUltraMulRel_mk_iff _ G L k s t).2 (ht.mono fun _ hi => hi.2)⟩

end NormalSubgroupWindow
end LocalGroupAlgebra
end DirectedCycles
