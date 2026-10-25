module

public import DirectedCycles.SignedCoordinateBox
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- Uniform shrinking loses only a fixed factor in each signed coordinate. -/
theorem signed_coordinate_shrink_bound (n T : ℕ) (hT : 0 < T) :
    2*n+1 ≤ (2*T)*(2*(n/T)+1) := by
  have hh : n < (n/T+1)*T := (Nat.div_lt_iff_lt_mul hT).1 (Nat.lt_succ_self _)
  nlinarith [Nat.zero_le (T*(n/T))]

theorem signed_box_shrink_bound {r : ℕ} (N : Fin r → ℕ) {T : ℕ} (hT : 0 < T) :
    (∏ i, (2*N i+1)) ≤ (2*T)^r * ∏ i, (2*(N i/T)+1) := by
  calc
    (∏ i, (2*N i+1)) ≤ ∏ i, ((2*T)*(2*(N i/T)+1)) :=
      Finset.prod_le_prod (fun i _ => signed_coordinate_shrink_bound (N i) T hT)
    _ = (2*T)^r * ∏ i, (2*(N i/T)+1) := by
      rw [Finset.prod_mul_distrib]
      simp

/-- A factor of at least three leaves the central interval within the
strict properness range, including small positive original lengths. -/
theorem twice_shrunk_length_lt {n T : ℕ} (hn : 0 < n) (hT : 3 ≤ T) : 2*(n/T) < n := by
  have hh := Nat.div_mul_le_self n T
  by_cases hz : n/T = 0
  · simp only [hz,mul_zero]
    exact hn
  · have hq : 0 < n/T := Nat.pos_of_ne_zero hz
    nlinarith

/-- Fixed integer shrinking preserves unbounded coordinate lengths. -/
theorem tendsto_nat_shrunk_length {ι : Type*} {F : Filter ι} {N : ι → ℕ}
    (hN : Filter.Tendsto N F Filter.atTop) {T : ℕ} (hT : 0 < T) :
    Filter.Tendsto (fun i => N i/T) F Filter.atTop := by
  have hdiv : Filter.Tendsto (fun n : ℕ => n/T) Filter.atTop Filter.atTop :=
    le_of_eq (Filter.map_div_atTop_eq_nat T hT)
  exact hdiv.comp hN

/-- The central fibre and quotient box density combine after one uniform
shrinking, without a separate upper bound on the word progression. -/
theorem central_box_density {r a q p J Jq n T : ℕ} (N : Fin r → ℕ)
    (hT : 0 < T) (ha : a ≤ J*q*p) (hq : q ≤ Jq * ∏ i, (2*N i+1))
    (hp : p ≤ 2*n+1) :
    a ≤ (J*Jq*(2*T)^(r+1)) * ((∏ i, (2*(N i/T)+1))*(2*(n/T)+1)) := by
  have hb := signed_box_shrink_bound N hT
  have hn := signed_coordinate_shrink_bound n T hT
  calc
    a ≤ J*q*p := ha
    _ ≤ J*(Jq*∏ i, (2*N i+1))*(2*n+1) := Nat.mul_le_mul (Nat.mul_le_mul_left J hq) hp
    _ ≤ J*(Jq*((2*T)^r*∏ i, (2*(N i/T)+1)))*((2*T)*(2*(n/T)+1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left J (Nat.mul_le_mul_left Jq hb)) hn
    _ = _ := by rw [pow_succ]; ring
end DirectedCycles
