module

public import DirectedCycles.LocalInternalSetLogic
public import DirectedCycles.LocalGroupHom

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*)

/-- If every variable-index ultraproduct point of the segments lies in an
internal set, all finite segment points belong eventually and simultaneously. -/
theorem local_uniform_segment_membership (B : ∀ i, Set (G i))
    (s : ∀ i, ℕ → G i) (M : ι → ℕ)
    (hmem : ∀ n : ι → ℕ, (∀ᶠ i in (U : Filter ι), n i ≤ M i) →
      localUltraMk (U : Filter ι) G (fun i => s i (n i)) ∈ localUltraSet (U : Filter ι) G B) :
    ∀ᶠ i in (U : Filter ι), ∀ n ≤ M i, s i n ∈ B i := by
  classical
  by_contra h
  have hbad : ∀ᶠ i in (U : Filter ι), ∃ n ≤ M i, s i n ∉ B i := by
    have hh := Ultrafilter.eventually_not.mpr h
    filter_upwards [hh] with i hi
    obtain ⟨n,hn⟩ := not_forall.mp hi
    exact ⟨n,not_imp.mp hn⟩
  let n : ι → ℕ := fun i => if hi : ∃ n ≤ M i, s i n ∉ B i then Classical.choose hi else 0
  have hn : ∀ᶠ i in (U : Filter ι), n i ≤ M i ∧ s i (n i) ∉ B i := by
    filter_upwards [hbad] with i hi
    dsimp only [n]
    rw [dite_eq_left hi]
    exact Classical.choose_spec hi
  have hm := (localUltraMk_mem_iff (U : Filter ι) G B _).1 (hmem n (hn.mono fun _ h => h.1))
  obtain ⟨i,hni,hmi⟩ := (hn.and hm).exists
  exact hni.2 hmi
end DirectedCycles
