module

public import DirectedCycles.LocalPowerTrappingTransfer
public import DirectedCycles.LocalInternalSetLogic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- A fixed finite power-trapping implication in the actual ultraproduct
forces the same implication at almost every finite component. -/
theorem localUltra_power_trapping_eventually (A B : ∀ i, Set (G i)) (m : ℕ)
    (htrap : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ m →
      (localUltraAlgebra (U : Filter ι) G L).PowerIn (localUltraSet (U : Filter ι) G B) x j) →
      x ∈ localUltraSet (U : Filter ι) G A) :
    ∀ᶠ i in (U : Filter ι), ∀ x,
      (∀ j : ℕ, 1 ≤ j → j ≤ m → (L i).PowerIn (B i) x j) → x ∈ A i := by
  classical
  by_contra hn
  have hbad := Ultrafilter.eventually_not.mpr hn
  have hex : ∀ i, ∃ x : G i,
      (¬ (∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ m → (L i).PowerIn (B i) x j) → x ∈ A i)) →
      (∀ j : ℕ, 1 ≤ j → j ≤ m → (L i).PowerIn (B i) x j) ∧ x ∉ A i := by
    intro i
    by_cases hi : ¬ (∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ m → (L i).PowerIn (B i) x j) → x ∈ A i)
    · obtain ⟨x,hx,hxa⟩ := by simpa only [not_forall,not_imp] using hi
      exact ⟨x,fun _ => ⟨hx,hxa⟩⟩
    · exact ⟨(L i).one,fun h => (hi h).elim⟩
  choose x hx using hex
  have hall := hbad.mono fun i hi => hx i hi
  have hxin := htrap (localUltraMk (U : Filter ι) G x) (by
    intro j hj hjm
    exact (localUltraPowerIn_mk_iff (U : Filter ι) G L B x j).2 (hall.mono fun _ hi => hi.1 j hj hjm))
  have hin := (localUltraMk_mem_iff (U : Filter ι) G A x).1 hxin
  obtain ⟨i,hi,hbi⟩ := (hin.and hall).exists
  exact hbi.2 hi
end DirectedCycles
