import DirectedCycles.ChosenLiftInput
import DirectedCycles.RoundSpanning

set_option autoImplicit false
namespace DirectedCycles

/-- The normalization of a quotient cycle preserves its additive spanning
property. This verifies the invariant for the actual selected source labels. -/
theorem cycleRunData_prefix_spanning {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (S : Set Q) (C : Cycle (CayleyDigraph S))
    (l : Fin C.length → ℕ) (s : Fin C.length → G)
    (hstep : ∀ i, C.vertex (finRotate C.length i) = C.vertex i*q (s i))
    (D : ℕ) (hspan : SpansTruncation D (Set.range C.vertex)) :
    SpansTruncation D (Set.range (fun i : Fin (cycleRunData l s).length =>
      q (cycleLabelPrefixes (cycleRunData l s) i.castSucc))) := by
  let zero : Fin C.length := ⟨0,by have := C.two_le; omega⟩
  apply spansTruncation_of_left_translate D (Set.range C.vertex) _ (C.vertex zero)⁻¹ hspan
  rintro x ⟨i,rfl⟩
  refine ⟨⟨i.val,by simpa only [cycleRunData_length] using i.isLt⟩,?_⟩
  change q (((cycleRunData l s).map Prod.snd).take i.val).prod = _
  rw [cycleRunData_snd]
  exact cayley_cycle_prefixes q S C s hstep i

theorem exists_chosen_lift_input_spanning {G : Type*} [Group G] [Finite G]
    (a : G) (S : Set G) (D : ℕ)
    (hh : 8*D+4 < Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)))
    (C : Cycle (CayleyDigraph ((QuotientGroup.mk' (elementClosure a)) '' S))) :
    ∃ input : ChosenLiftInput a S D, input.data.length = C.length ∧
      (SpansTruncation D (Set.range C.vertex) →
        SpansTruncation D (Set.range (fun i : Fin input.data.length =>
          QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes input.data i.castSucc)))) := by
  let q := QuotientGroup.mk' (elementClosure a)
  obtain ⟨s,hs,hstep⟩ := cayley_cycle_labels q S C
  have hclose := cayley_cycle_word_closes q (q '' S) C s hstep
  have hmem : (List.ofFn s).prod ∈ elementClosure a := (QuotientGroup.eq_one_iff _).mp hclose
  obtain ⟨nu,hnu⟩ := elementClosure_quotient_power a (List.ofFn s).prod hmem
  obtain ⟨l,hl,hcong,hT⟩ := choose_run_lengths C.length
    (Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a))) D C.two_le hh nu
  refine ⟨{
    data := cycleRunData l s
    two_le_length := by simpa only [cycleRunData_length] using C.two_le
    nu := nu
    endpoint := by simpa only [cycleRunData_snd] using hnu
    congruence := by simpa only [cycleRunData_sum,Nat.cast_sum,Nat.cast_add] using hcong
    prefixes := cycleRunData_prefix_injective q (q '' S) C l s hstep
    bounds := ?_
    labels := ?_
    quarter_bound := by simpa only [cycleRunData_length,cycleRunData_sum,Nat.cast_sum] using hT
  },cycleRunData_length l s,?_⟩
  · intro i
    rw [cycleRunData_get]
    have hi : i.val < C.length := by simpa only [cycleRunData_length] using i.isLt
    have hli := hl ⟨i.val,hi⟩
    exact ⟨hli.1,by omega⟩
  · intro i
    rw [cycleRunData_get]
    exact hs _
  · exact cycleRunData_prefix_spanning q (q '' S) C l s hstep D

end DirectedCycles
