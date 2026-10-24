import DirectedCycles.AuxiliaryLayerBound
import DirectedCycles.LayerCycleExpansion
import DirectedCycles.AuxiliaryGroupIndex
import DirectedCycles.DensityRecurrence
import DirectedCycles.LiftCardinalities

set_option autoImplicit false
namespace DirectedCycles

/-- Theorem 5.1 with explicit uniform constants. D is written n+1. The layer
hypothesis is used only for at least two layers, and the numerical proof only
needs eta nonnegative. These are weaker hypotheses than the manuscript's. -/
theorem directed_cycle_lifting {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (a : G) (S : Set G) (ha : a ∈ S) (r c n : ℕ)
    (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c) (hn : c ≤ n)
    (hh : 8*(n+1)+4 < Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)))
    (Q : Cycle (CayleyDigraph ((QuotientGroup.mk' (elementClosure a)) '' S)))
    (b eta : ℝ) (hb : 0 < b) (heta : 0 ≤ eta)
    (hlayer : ∀ U : Subgroup (elementCommutators a), LayerCycleLowerBound U b eta) :
    ∃ C : Cycle (CayleyDigraph S), C.ClosedUnderGenerator a ∧
      b/(4*(auxiliaryIndexConstant r c n : ℝ))*
        ((Q.length : ℝ)/Nat.card (G ⧸ elementClosure a))^(auxiliaryIndexExponent r c n+1)*
        (Nat.card (elementCommutators a) : ℝ)^(-eta) ≤ (C.length : ℝ)/Nat.card G := by
  obtain ⟨input,hlen⟩ := exists_chosen_lift_input a S (n+1) hh Q
  obtain ⟨QA,hQA⟩ := chosen_auxiliary_long_cycle a S (n+1) input b eta hlayer
  obtain ⟨C,hC,hA,_⟩ := expanding_layer_cycle a (n+1) input.data input.nonempty input.nu
    input.endpoint input.congruence input.prefixes input.bounds S ha input.labels QA
  refine ⟨C,hA,?_⟩
  let B := elementCommutators a
  let U := cyclicAuxiliaryGroup a (n+1) input.data input.nonempty
  let I := (U.subgroupOf B).index
  let N := Nat.card (G ⧸ elementClosure a)
  let h := Nat.card (elementClosure a ⧸ B.subgroupOf (elementClosure a))
  let T := (slotBaseline (cyclicLiftSlots a (n+1) input.data)).length
  have hU : U ≤ B := cyclicAuxiliaryGroup_le_of_congruence a (n+1) input.data input.nonempty
    input.nu input.endpoint input.congruence
  have hindex := auxiliary_group_density_index a r c n hr hc hn input.data input.nonempty input.nu
    input.prefixes input.endpoint input.congruence
  have hBpos : (0 : ℝ) < Nat.card B := by exact_mod_cast (Nat.card_pos (α := B))
  have hUpos : (0 : ℝ) < Nat.card U := by exact_mod_cast (Nat.card_pos (α := U))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.card_pos (α := G ⧸ elementClosure a))
  have hhpos : (0 : ℝ) < h := by
    exact_mod_cast (Nat.card_pos (α := elementClosure a ⧸ B.subgroupOf (elementClosure a)))
  have hell : (0 : ℝ) < input.data.length := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) input.two_le_length)
  have hJ : (0 : ℝ) < auxiliaryIndexConstant r c n := by exact_mod_cast auxiliaryIndexConstant_pos r c n
  have hI : (1 : ℝ) ≤ I := by
    have hi : 1 ≤ I := Nat.one_le_iff_ne_zero.mpr (Subgroup.index_ne_zero_of_finite (H := U.subgroupOf B))
    exact_mod_cast hi
  have hcard : (Nat.card B : ℝ) = (I : ℝ)*Nat.card U := by
    exact_mod_cast subgroupOf_index_card B U hU
  have hT : (input.data.length : ℝ)*h/4 ≤ T := by
    have ht := input.quarter_bound.le
    simpa only [T,slotBaseline_length,cyclicLiftSlots_length,h,B] using ht
  have hlength : b*T*(Nat.card U : ℝ)^(1-eta) ≤ C.length :=
    hQA.trans (by exact_mod_cast hC)
  have hcalc := directed_lift_density_recurrence (C.length : ℝ) b T input.data.length h
    (Nat.card B) (Nat.card U) I N (auxiliaryIndexConstant r c n) eta (auxiliaryIndexExponent r c n)
    hb hell hhpos hBpos hUpos hNpos hJ heta hcard hI hindex hT hlength
  have hG : (Nat.card G : ℝ) = (N : ℝ)*h*Nat.card B := by
    exact_mod_cast elementClosure_card_factorization a
  rw [← hG,hlen] at hcalc
  exact hcalc

/-- Both explicit uniform constants have the lower bounds required in 5.1. -/
theorem directed_lifting_constants (r c n : ℕ) :
    1 ≤ 4*auxiliaryIndexConstant r c n ∧ 1 ≤ auxiliaryIndexExponent r c n := by
  have := auxiliaryIndexConstant_pos r c n
  have := auxiliaryIndexExponent_pos r c n
  constructor <;> omega

end DirectedCycles
