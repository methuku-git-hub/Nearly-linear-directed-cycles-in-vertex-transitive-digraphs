import DirectedCycles.DifferenceConstraints
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
namespace DirectedCycles

/-- Residues excluded by the lower and upper run-length bounds. -/
def badRunResidues (h D : ℕ) : Finset (ZMod h) :=
  ((Finset.range ((h+7)/8)).image (fun n : ℕ => (n : ZMod h))) ∪
    ((Finset.Ico (h-2*D-1) h).image (fun n : ℕ => (n : ZMod h)))

theorem badRunResidues_card (h D : ℕ) (hh : 2*D+1 ≤ h) :
    (badRunResidues h D).card ≤ (h+7)/8 + 2*D+1 := by
  apply (Finset.card_union_le _ _).trans
  have hlow := Finset.card_image_le (s := Finset.range ((h+7)/8))
    (f := fun n : ℕ => (n : ZMod h))
  have hhigh := Finset.card_image_le (s := Finset.Ico (h-2*D-1) h)
    (f := fun n : ℕ => (n : ZMod h))
  simp only [Finset.card_range,Nat.card_Ico] at hlow hhigh
  omega

theorem run_bounds_of_not_bad (h D : ℕ) [NeZero h] (hh : 2*D+2 ≤ h)
    (l : ZMod h) (hl : l ∉ badRunResidues h D) :
    (h+7)/8 ≤ l.val ∧ l.val ≤ h-2*D-2 := by
  have hn := ZMod.val_lt l
  have hc := ZMod.natCast_zmod_val l
  constructor
  · by_contra he
    exact hl (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨l.val,Finset.mem_range.mpr (by omega),hc⟩))
  · by_contra he
    exact hl (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨l.val,Finset.mem_Ico.mpr ⟨by omega,hn⟩,hc⟩))

theorem separated_run_forbidden_budget (h q D : ℕ)
    (hh : 8*(q+1)*(D+1) < h) :
    2*((h+7)/8+2*D+1) + 2*q*(2*D+1) < h := by
  have hceil : 8*((h+7)/8) ≤ h+7 := Nat.mul_div_le _ _
  nlinarith

theorem separated_run_lower (h q D : ℕ) (hh : 8*(q+1)*(D+1) < h) :
    D ≤ (h+7)/8 ∧ 2*D+2 ≤ h := by
  have hceil : h ≤ 8*((h+7)/8) := by omega
  constructor <;> nlinarith

end DirectedCycles
