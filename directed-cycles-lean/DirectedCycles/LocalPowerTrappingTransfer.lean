import DirectedCycles.LocalUltraproductEscape
import DirectedCycles.LocalDivision

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

theorem localUltra_divisionClosed_eventually
    (hd : ∀ᶠ i in (U : Filter ι), (L i).DivisionClosed) :
    (localUltraAlgebra (U : Filter ι) G L).DivisionClosed where
  left := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro a b c hm
    apply (localUltraMulRel_mk_iff (U : Filter ι) G L _ _ _).2
    have h := (localUltraMulRel_mk_iff (U : Filter ι) G L a b c).1 hm
    filter_upwards [hd,h] with i hi hmi
    exact hi.left hmi
  right := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro a b c hm
    apply (localUltraMulRel_mk_iff (U : Filter ι) G L _ _ _).2
    have h := (localUltraMulRel_mk_iff (U : Filter ι) G L a b c).1 hm
    filter_upwards [hd,h] with i hi hmi
    exact hi.right hmi

theorem localUltra_reversible_eventually
    (hr : ∀ᶠ i in (U : Filter ι), (L i).Reversible) :
    (localUltraAlgebra (U : Filter ι) G L).Reversible := by
  intro a b c
  refine Quotient.inductionOn₃ a b c ?_
  intro a b c hm
  apply (localUltraMulRel_mk_iff (U : Filter ι) G L _ _ _).2
  have h := (localUltraMulRel_mk_iff (U : Filter ι) G L a b c).1 hm
  filter_upwards [hr,h] with i hi hmi
  exact hi hmi

/-- A fixed finite power-trapping condition transfers with its quantifiers
intact. Only finitely many component power conditions are intersected. -/
theorem localUltra_power_trapping (A B : ∀ i, Set (G i)) (m : ℕ)
    (htrap : ∀ᶠ i in (U : Filter ι), ∀ x,
      (∀ j : ℕ, 1 ≤ j → j ≤ m → (L i).PowerIn (B i) x j) → x ∈ A i) :
    ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ m →
      (localUltraAlgebra (U : Filter ι) G L).PowerIn (localUltraSet (U : Filter ι) G B) x j) →
      x ∈ localUltraSet (U : Filter ι) G A := by
  intro x hx
  obtain ⟨a,rfl⟩ := Quotient.exists_rep x
  have each : ∀ j : Fin (m+1), ∀ᶠ i in (U : Filter ι),
      1 ≤ j.val → (L i).PowerIn (B i) (a i) j.val := by
    intro j
    by_cases hj : 1 ≤ j.val
    · exact ((localUltraPowerIn_mk_iff (U : Filter ι) G L B a j.val).1
        (hx j.val hj (by omega))).mono fun _ hi _ => hi
    · exact Filter.Eventually.of_forall fun _ h => (hj h).elim
  apply (localUltraMk_mem_iff (U : Filter ι) G A a).2
  filter_upwards [htrap,Filter.eventually_all.2 each] with i hi hpi
  exact hi (a i) (fun j hj hjm => hpi ⟨j,by omega⟩ hj)
end DirectedCycles
