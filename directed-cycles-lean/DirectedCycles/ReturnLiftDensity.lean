module

public import DirectedCycles.BasedReturnLifting
public import DirectedCycles.AuxiliaryLayerBound
public import DirectedCycles.DensityRecurrence
public import DirectedCycles.LiftCardinalities

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

namespace ReturnLiftConstruction
variable {G V : Type*} [Group G] [Finite G] {X : Digraph V} {a : G} {S : Set G}
  {C : Cycle (CayleyDigraph (QuotientGroup.mk' (elementClosure a) '' S))} {r c n : ℕ}

theorem two_le_layers (R : ReturnLiftConstruction X a S C r c n) :
    2 ≤ (slotBaseline (cyclicLiftSlots a (n+1) (cycleRunData R.runs R.labels))).length := by
  rw [slotBaseline_length,cyclicLiftSlots_length,cycleRunData_sum]
  refine C.two_le.trans ?_
  calc C.length = (∑ _i : Fin C.length, (1 : ℕ)) := by simp
       _ ≤ (∑ i : Fin C.length, (R.runs i+1)) := Finset.sum_le_sum (fun i _ => Nat.le_add_left 1 (R.runs i))

/-- The exact large-return density calculation, with the factor 8 arising
from the proved run packing. -/
theorem density_bound (R : ReturnLiftConstruction X a S C r c n)
    (b eta : ℝ) (hb : 0 < b) (heta : 0 ≤ eta)
    (hlayer : ∀ U : Subgroup (elementCommutators a), LayerCycleLowerBound U b eta) :
    ∃ L : Cycle X,
      b/(8*(auxiliaryIndexConstant r c n : ℝ))*
        ((C.length : ℝ)/Nat.card (G ⧸ elementClosure a))^(auxiliaryIndexExponent r c n+1)*
        (Nat.card (elementCommutators a) : ℝ)^(-eta) ≤ (L.length : ℝ)/Nat.card G := by
  let B := elementCommutators a
  let U := cyclicAuxiliaryGroup a (n+1) (cycleRunData R.runs R.labels) R.nonempty
  let T := (slotBaseline (cyclicLiftSlots a (n+1) (cycleRunData R.runs R.labels))).length
  let e := Subgroup.subgroupOfEquivOfLe R.group_le
  have hbound : LayerCycleLowerBound U b eta :=
    layerCycleLowerBound_equiv e.symm b eta (hlayer (U.subgroupOf B))
  obtain ⟨QA,hQA⟩ := hbound T R.two_le_layers _
    (cyclicAuxiliary_labels_nonempty a (n+1) (cycleRunData R.runs R.labels) R.nonempty) R.connected
  obtain ⟨L,hL⟩ := R.lift QA
  refine ⟨L,?_⟩
  let idx := (U.subgroupOf B).index
  let N := Nat.card (G ⧸ elementClosure a)
  let h := orderOf (QuotientGroup.mk' (elementCommutators a) a)
  have hBpos : (0 : ℝ) < Nat.card B := by exact_mod_cast (Nat.card_pos (α := B))
  have hUpos : (0 : ℝ) < Nat.card U := by exact_mod_cast (Nat.card_pos (α := U))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.card_pos (α := G ⧸ elementClosure a))
  have hhpos : (0 : ℝ) < h := by exact_mod_cast orderOf_pos (QuotientGroup.mk' (elementCommutators a) a)
  have hell : (0 : ℝ) < C.length := by exact_mod_cast (by have := C.two_le; omega : 0 < C.length)
  have hJ : (0 : ℝ) < auxiliaryIndexConstant r c n := by exact_mod_cast auxiliaryIndexConstant_pos r c n
  have hI : (1 : ℝ) ≤ idx := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Subgroup.index_ne_zero_of_finite (H := U.subgroupOf B))
  have hcard : (Nat.card B : ℝ) = (idx : ℝ)*Nat.card U := by
    exact_mod_cast subgroupOf_index_card B U R.group_le
  have hT : (C.length : ℝ)*h/4 ≤ 2*T := by
    have hh : (C.length : ℝ)*h ≤ 8*T := by exact_mod_cast R.layers
    linarith
  have hlength : b/2*(2*T)*(Nat.card U : ℝ)^(1-eta) ≤ L.length := by
    have hh : b*T*(Nat.card U : ℝ)^(1-eta) ≤ L.length := hQA.trans (by exact_mod_cast hL)
    nlinarith only [hh]
  have hcalc := directed_lift_density_recurrence (L.length : ℝ) (b/2) (2*T) C.length h
    (Nat.card B) (Nat.card U) idx N (auxiliaryIndexConstant r c n) eta (auxiliaryIndexExponent r c n)
    (by positivity) hell hhpos hBpos hUpos hNpos hJ heta hcard hI R.index_bound hT hlength
  have hG : (Nat.card G : ℝ) = (N : ℝ)*h*Nat.card B := by
    have hc := elementClosure_card_factorization a
    rw [elementClosure_factor_card_eq_orderOf] at hc
    exact_mod_cast hc
  rw [← hG] at hcalc
  have he : b/2/(4*(auxiliaryIndexConstant r c n : ℝ)) = b/(8*auxiliaryIndexConstant r c n) := by ring
  rw [he] at hcalc
  exact hcalc

end ReturnLiftConstruction
end DirectedCycles
