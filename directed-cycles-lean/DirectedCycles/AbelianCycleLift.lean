module

public import DirectedCycles.AbelianAuxiliaryCycle
public import DirectedCycles.SpanningLiftInput
public import DirectedCycles.LayerCycleExpansion

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The abelian lift has no auxiliary index loss: the constructed auxiliary
group is trivial. The length and spanning conclusions concern its actual cycle. -/
theorem abelian_cycle_lift {G : Type*} [CommGroup G] [Finite G]
    (a : G) (S : Set G) (ha : a ∈ S) (D : ℕ) (horder : 8*D+4 < orderOf a)
    (Q : Cycle (CayleyDigraph ((QuotientGroup.mk' (elementClosure a)) '' S))) :
    ∃ C : Cycle (CayleyDigraph S),
      (Q.length : ℝ)*orderOf a/4 ≤ C.length ∧ C.ClosedUnderGenerator a ∧
      (SpansTruncation D (Set.range Q.vertex) → SpansTruncation D (C.generatorTails a)) := by
  have hh : 8*D+4 < Nat.card (elementClosure a ⧸
      (elementCommutators a).subgroupOf (elementClosure a)) := by
    rwa [abelian_closure_factor_order]
  obtain ⟨input,hlen,hspan⟩ := exists_chosen_lift_input_spanning a S D hh Q
  obtain ⟨QA,hQA,hfull⟩ := abelian_auxiliary_cycle a S D input
  obtain ⟨C,hC,hA,hsp⟩ := expanding_layer_cycle a D input.data input.nonempty input.nu
    input.endpoint input.congruence input.prefixes input.bounds S ha input.labels QA
  refine ⟨C,?_,hA,?_⟩
  · have hquarter := input.quarter_bound.le
    rw [abelian_closure_factor_order,hlen] at hquarter
    have hsum : (input.data.map (fun z => z.1+1)).sum ≤ C.length := by
      simpa only [slotBaseline_length,cyclicLiftSlots_length] using hQA.trans hC
    exact hquarter.trans (by exact_mod_cast hsum)
  · intro hQ
    apply hsp (hspan hQ)
    intro z
    rw [hfull]
    exact spansTruncation_univ D

end DirectedCycles
