module

public import DirectedCycles.CycleRunData
public import DirectedCycles.RunLengthChoice
public import DirectedCycles.BaselineClosureCongruence

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Concrete data selected from the quotient cycle for Theorem 5.1. Every
field is constructed by `exists_chosen_lift_input`; none is an external input. -/
structure ChosenLiftInput {G : Type*} [Group G] [Finite G] (a : G) (S : Set G) (D : ℕ) where
  data : List (ℕ × G)
  two_le_length : 2 ≤ data.length
  nu : ℤ
  endpoint : QuotientGroup.mk' (elementCommutators a) (data.map Prod.snd).prod =
    (QuotientGroup.mk' (elementCommutators a) a)^nu
  congruence : (Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)) : ℤ) ∣
    ((data.map (fun z => z.1+D)).sum : ℤ)+nu
  prefixes : Function.Injective (fun i : Fin data.length =>
    QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc))
  bounds : ∀ i : Fin data.length, D ≤ (data[i.val]).1 ∧ (data[i.val]).1+2*D+2 ≤
    Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a))
  labels : ∀ i : Fin data.length, (data[i.val]).2 ∈ S
  quarter_bound : (data.length : ℝ)*
    Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a))/4 <
      (((data.map (fun z => (z.1+1 : ℕ))).sum : ℕ) : ℝ)

/-- An arbitrary quotient cycle supplies valid lift data with the same
quotient-cycle length, including the residue correction and its length bound. -/
theorem exists_chosen_lift_input {G : Type*} [Group G] [Finite G]
    (a : G) (S : Set G) (D : ℕ)
    (hh : 8*D+4 < Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)))
    (C : Cycle (CayleyDigraph ((QuotientGroup.mk' (elementClosure a)) '' S))) :
    ∃ input : ChosenLiftInput a S D, input.data.length = C.length := by
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
  },cycleRunData_length l s⟩
  · intro i
    rw [cycleRunData_get]
    have hi : i.val < C.length := by simpa only [cycleRunData_length] using i.isLt
    have hli := hl ⟨i.val,hi⟩
    exact ⟨hli.1,by omega⟩
  · intro i
    rw [cycleRunData_get]
    exact hs _

theorem ChosenLiftInput.nonempty {G : Type*} [Group G] [Finite G]
    {a : G} {S : Set G} {D : ℕ} (input : ChosenLiftInput a S D) : input.data ≠ [] := by
  intro he
  have h := input.two_le_length
  rw [he,List.length_nil] at h
  omega

end DirectedCycles
