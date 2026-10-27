module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles

/-- A positive small step can be normalised by a natural power with total
size between half the target scale and the target scale. -/
theorem normalized_power_scale_bounds {R a : ℝ} (hR : 0 < R) (ha : 0 < a) (haR : a ≤ R/2) :
    0 < ⌊R/a⌋₊ ∧ R/2 ≤ (⌊R/a⌋₊ : ℝ)*a ∧ (⌊R/a⌋₊ : ℝ)*a ≤ R := by
  have hratio : 0 ≤ R/a := (div_pos hR ha).le
  have hn1 : 1 ≤ ⌊R/a⌋₊ := (Nat.one_le_floor_iff _).mpr ((le_div_iff₀ ha).mpr (by linarith))
  have hlo := (div_lt_iff₀ ha).mp (Nat.lt_floor_add_one (R/a))
  have hhi := (le_div_iff₀ ha).mp (Nat.floor_le hratio)
  exact ⟨by omega,by nlinarith,hhi⟩

/-- As positive step sizes tend to zero, their actual floor normalisations
tend to infinity. -/
theorem normalized_power_scale_tendsto {ι : Type*} {l : Filter ι} {a : ι → ℝ} {R : ℝ}
    (hR : 0 < R) (ha : ∀ᶠ i in l, 0 < a i) (hzero : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => ⌊R/a i⌋₊) l atTop := by
  apply tendsto_atTop.mpr
  intro n
  have hε : 0 < R/((n : ℝ)+1) := by positivity
  have hev : ∀ᶠ i in l, a i < R/((n : ℝ)+1) := hzero.eventually (gt_mem_nhds hε)
  filter_upwards [ha,hev] with i hi hai
  apply (Nat.le_floor_iff (div_nonneg hR.le hi.le)).mpr
  apply (le_div_iff₀ hi).mpr
  have h := (lt_div_iff₀ (show 0 < (n : ℝ)+1 by positivity)).mp hai
  nlinarith
end DirectedCycles
