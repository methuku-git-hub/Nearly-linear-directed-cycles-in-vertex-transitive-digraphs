import DirectedCycles.CommutatorWeights
import DirectedCycles.RelativeCentralSeries

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- Ambient commutator weight increases the relative central-series index
by the same amount. The three-subgroup lemma supplies the induction step. -/
theorem relative_lowerSeries_commutator_le {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (i j : ℕ) :
    ⁅relativeSeries N i, lowerSeries G j⁆ ≤ relativeSeries N (i+j+1) := by
  induction j generalizing i with
  | zero =>
    change ⁅relativeSeries N i,(⊤ : Subgroup G)⁆ ≤ ⁅relativeSeries N i,(⊤ : Subgroup G)⁆
    exact le_rfl
  | succ j ih =>
    rw [Subgroup.commutator_comm]
    change ⁅⁅lowerSeries G j,(⊤ : Subgroup G)⁆,relativeSeries N i⁆ ≤ _
    apply commutator_commutator_le_of_rotate
    · rw [Subgroup.commutator_comm (⊤ : Subgroup G)]
      change ⁅relativeSeries N (i+1),lowerSeries G j⁆ ≤ relativeSeries N (i+(j+1)+1)
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (i+1)
    · have hh := Subgroup.commutator_mono (ih i) (le_refl (⊤ : Subgroup G))
      exact hh

/-- Derived-group inputs gain two relative commutator levels. -/
theorem relative_derived_commutator_le {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (i : ℕ) :
    ⁅relativeSeries N i,commutator G⁆ ≤ relativeSeries N (i+2) := by
  simpa only [lowerSeries,Subgroup.top_lowerCentralSeries_one,Nat.add_assoc]
    using relative_lowerSeries_commutator_le N i 1

/-- The terminal nonzero relative term is central. -/
theorem relativeSeries_central_of_next_eq_bot {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (i : ℕ) (h : relativeSeries N (i+1) = ⊥) :
    relativeSeries N i ≤ Subgroup.center G :=
  Subgroup.commutator_top_right_eq_bot_iff_le_center.mp h

end DirectedCycles
