module

public import DirectedCycles.DensityPowerArithmetic
public import Mathlib.GroupTheory.Index

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A bounded normal quotient loses at most its kernel order in the
uniform length constant. -/
theorem small_kernel_length {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (b M eps ell L : ℝ)
    (hb : 0 ≤ b) (hKM : (Nat.card K : ℝ) ≤ M) (heps : 0 ≤ eps)
    (hell : b*(Nat.card (G ⧸ K) : ℝ)^(1-eps) ≤ ell) (hL : ell ≤ L) :
    b/M*(Nat.card G : ℝ)^(1-eps) ≤ L := by
  have hq : (0 : ℝ) < Nat.card (G ⧸ K) := by exact_mod_cast (Nat.card_pos (α := G ⧸ K))
  have hk : (1 : ℝ) ≤ Nat.card K := by exact_mod_cast (Nat.card_pos (α := K))
  have hg : (0 : ℝ) < Nat.card G := by exact_mod_cast (Nat.card_pos (α := G))
  have hcard : (Nat.card G : ℝ) = (Nat.card (G ⧸ K) : ℝ)*Nat.card K := by
    have hc := K.index_mul_card
    rw [Subgroup.index_eq_card] at hc
    exact_mod_cast hc.symm
  have hdens := small_kernel_density b (Nat.card (G ⧸ K)) (Nat.card K) M (Nat.card G) eps ell L
    hb hq hk hKM hcard heps ((length_bound_iff_density_bound b _ eps ell hq).mp hell) hL
  exact (length_bound_iff_density_bound (b/M) _ eps L hg).mpr hdens

end DirectedCycles
