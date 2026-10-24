import DirectedCycles.LocalNormalWindowUltraproduct
import DirectedCycles.LocalCongruenceUltraproduct

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace NormalSubgroupWindow
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (H S : ∀ i, Set (G i)) (W : ∀ i, (L i).NormalSubgroupWindow (H i) (S i))
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)

abbrev componentCongruence (i : ι) := (W i).congruence (hd i) (hr i)
abbrev limitCongruence := (ultraproduct U G L H S W).congruence
  (localUltraAlgebra_divisionClosed (U : Filter ι) G L hd)
  (localUltraAlgebra_reversible (U : Filter ι) G L hr)
abbrev componentUltraCongruence := LocalGroupCongruence.ultraproduct (U : Filter ι) (fun i => S i)
  (fun i => (W i).restricted) (componentCongruence G L H S W hd hr)
noncomputable abbrev windowEquiv := localUltraWindowEquiv (U : Filter ι) G L S (fun i => (W i).one_mem)

/-- The actual internal normal-subgroup orbit relation is precisely the
component quotient kernel relation under the window identification. -/
theorem ultra_relation_iff (a b : LocalUltraproduct (U : Filter ι) (fun i => S i)) :
    (componentUltraCongruence U G L H S W hd hr).toSetoid.r a b ↔
      (limitCongruence U G L H S W hd hr).toSetoid.r
        (windowEquiv U G L H S W a) (windowEquiv U G L H S W b) := by
  classical
  obtain ⟨a,rfl⟩ := Quotient.exists_rep a
  obtain ⟨b,rfl⟩ := Quotient.exists_rep b
  change localUltraMk (U : Filter ι) (fun i => (componentCongruence G L H S W hd hr i).Carrier)
      (fun i => (componentCongruence G L H S W hd hr i).project (a i)) =
    localUltraMk (U : Filter ι) (fun i => (componentCongruence G L H S W hd hr i).Carrier)
      (fun i => (componentCongruence G L H S W hd hr i).project (b i)) ↔
    ∃ h ∈ localUltraSet (U : Filter ι) G H,
      (localUltraAlgebra (U : Filter ι) G L).mulRel h
        (localUltraMk (U : Filter ι) G (fun i => (b i).val))
        (localUltraMk (U : Filter ι) G (fun i => (a i).val))
  rw [localUltraMk_eq_iff]
  constructor
  · intro he
    have hex : ∀ᶠ i in (U : Filter ι), ∃ h ∈ H i, (L i).mulRel h (b i).val (a i).val :=
      he.mono fun _ hi => Quotient.exact hi
    let h : ∀ i, G i := fun i => if hi : ∃ h ∈ H i, (L i).mulRel h (b i).val (a i).val
      then Classical.choose hi else (L i).one
    have hh : ∀ᶠ i in (U : Filter ι), h i ∈ H i ∧ (L i).mulRel (h i) (b i).val (a i).val := by
      filter_upwards [hex] with i hi
      dsimp only [h]
      rw [dite_eq_left hi]
      exact Classical.choose_spec hi
    exact ⟨localUltraMk (U : Filter ι) G h,(localUltraMk_mem_iff _ G H h).2 (hh.mono fun _ hi => hi.1),
      (localUltraMulRel_mk_iff _ G L h (fun i => (b i).val) (fun i => (a i).val)).2 (hh.mono fun _ hi => hi.2)⟩
  · rintro ⟨h,⟨h,hh,rfl⟩,hm⟩
    have hm' := (localUltraMulRel_mk_iff (U : Filter ι) G L h (fun i => (b i).val) (fun i => (a i).val)).1 hm
    filter_upwards [hh,hm'] with i hi hmi
    exact Quotient.sound ⟨h i,hi,hmi⟩
end NormalSubgroupWindow
end LocalGroupAlgebra
end DirectedCycles
