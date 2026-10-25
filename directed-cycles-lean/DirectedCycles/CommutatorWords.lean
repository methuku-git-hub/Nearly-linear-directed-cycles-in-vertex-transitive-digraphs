module

public import DirectedCycles.RelativeCommutatorWeights
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

set_option autoImplicit false
open scoped commutatorElement Pointwise
namespace DirectedCycles

/-- Binary commutator forms with explicitly labelled leaves. -/
inductive CommutatorWord (α : Type*)
  | var : α → CommutatorWord α
  | bracket : CommutatorWord α → CommutatorWord α → CommutatorWord α

namespace CommutatorWord
variable {α : Type*}

def weight : CommutatorWord α → ℕ
  | .var _ => 1
  | .bracket a b => a.weight+b.weight

theorem weight_pos (w : CommutatorWord α) : 1 ≤ w.weight := by
  induction w with
  | var _ => exact le_rfl
  | bracket a b ha hb => change 1 ≤ a.weight+b.weight; omega

def eval {G : Type*} [Group G] (x : α → G) : CommutatorWord α → G
  | .var i => x i
  | .bracket a b => ⁅a.eval x,b.eval x⁆

theorem eval_mem_lowerSeries {G : Type*} [Group G] (w : CommutatorWord α) (x : α → G) :
    w.eval x ∈ lowerSeries G (w.weight-1) := by
  induction w with
  | var i => exact Subgroup.mem_top _
  | bracket a b ha hb =>
    have hh := lowerSeries_commutator_le (G := G) (a.weight-1) (b.weight-1)
      (Subgroup.commutator_mem_commutator ha hb)
    have he : (a.weight-1)+(b.weight-1)+1 = (a.weight+b.weight)-1 := by
      have := a.weight_pos
      have := b.weight_pos
      omega
    simpa only [he,eval,weight] using hh

theorem eval_eq_one_of_class_lt {G : Type*} [Group G] [Group.IsNilpotent G]
    (w : CommutatorWord α) (x : α → G) (c : ℕ)
    (hc : Group.nilpotencyClass G ≤ c) (hw : c < w.weight) : w.eval x = 1 := by
  have hbound := Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)
    (show c ≤ w.weight-1 by omega) (w.eval_mem_lowerSeries x)
  have he : lowerSeries G c = ⊥ := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc
  change w.eval x ∈ lowerSeries G c at hbound
  rw [he] at hbound
  exact hbound

end CommutatorWord

/-- A commutator form with one distinguished input and any number of
ordinary inputs. The distinguished input can occur on either side. -/
inductive MarkedCommutatorWord (α : Type*)
  | marked : MarkedCommutatorWord α
  | left : MarkedCommutatorWord α → CommutatorWord α → MarkedCommutatorWord α
  | right : CommutatorWord α → MarkedCommutatorWord α → MarkedCommutatorWord α

namespace MarkedCommutatorWord
variable {α : Type*}

def degree : MarkedCommutatorWord α → ℕ
  | .marked => 0
  | .left a b => a.degree+b.weight
  | .right a b => a.weight+b.degree

def eval {G : Type*} [Group G] (h : G) (x : α → G) : MarkedCommutatorWord α → G
  | .marked => h
  | .left a b => ⁅a.eval h x,b.eval x⁆
  | .right a b => ⁅a.eval x,b.eval h x⁆

theorem eval_mem_relativeSeries {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (w : MarkedCommutatorWord α) (h : G) (hh : h ∈ N) (x : α → G) :
    w.eval h x ∈ relativeSeries N w.degree := by
  induction w with
  | marked => exact hh
  | left a b ha =>
    have hb := b.eval_mem_lowerSeries x
    have hm := relative_lowerSeries_commutator_le N a.degree (b.weight-1)
      (Subgroup.commutator_mem_commutator ha hb)
    have he : a.degree+(b.weight-1)+1 = a.degree+b.weight := by
      have := b.weight_pos
      omega
    simpa only [he,eval,degree] using hm
  | right a b hb =>
    have ha := a.eval_mem_lowerSeries x
    have hm := Subgroup.commutator_mem_commutator ha hb
    rw [Subgroup.commutator_comm] at hm
    have hc := relative_lowerSeries_commutator_le N b.degree (a.weight-1) hm
    have he : b.degree+(a.weight-1)+1 = a.weight+b.degree := by
      have := a.weight_pos
      omega
    simpa only [he,eval,degree] using hc

theorem eval_eq_one_of_class_le {G : Type*} [Group G] [Group.IsNilpotent G]
    (N : Subgroup G) [N.Normal] (w : MarkedCommutatorWord α) (h : G) (hh : h ∈ N)
    (x : α → G) (c : ℕ) (hc : Group.nilpotencyClass G ≤ c) (hw : c ≤ w.degree) :
    w.eval h x = 1 := by
  have hv := relativeSeries_le_lower N w.degree (w.eval_mem_relativeSeries N h hh x)
  have hm := Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) hw hv
  have he : lowerSeries G c = ⊥ := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc
  change w.eval h x ∈ lowerSeries G c at hm
  rw [he] at hm
  exact hm

end MarkedCommutatorWord
end DirectedCycles
