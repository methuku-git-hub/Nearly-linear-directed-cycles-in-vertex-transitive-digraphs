module

public import DirectedCycles.NilpotentCycleBounds

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

theorem CayleySpanningBound.weaken {G : Type*} [Group G] [Finite G]
    {D : ℕ} {b b' eta eta' : ℝ} (h : CayleySpanningBound G D b eta)
    (hb : 0 ≤ b) (hbb : b' ≤ b) (heta : eta ≤ eta') : CayleySpanningBound G D b' eta' := by
  intro hnt S hS
  obtain ⟨C,hC,hspan⟩ := h hnt S hS
  have hcard : (1 : ℝ) ≤ Nat.card G := by exact_mod_cast (Nat.card_pos (α := G))
  refine ⟨C,?_,hspan⟩
  have hp := Real.rpow_le_rpow_of_exponent_le hcard (show 1-eta' ≤ 1-eta by linarith)
  exact (mul_le_mul hbb hp (Real.rpow_nonneg (zero_le_one.trans hcard) _) hb).trans hC

theorem LayerSpanningBound.weaken {G : Type*} [Group G] [Finite G]
    {D : ℕ} {b b' eta eta' : ℝ} (h : LayerSpanningBound G D b eta)
    (hb : 0 ≤ b) (hbb : b' ≤ b) (heta : eta ≤ eta') : LayerSpanningBound G D b' eta' := by
  intro T hT S hS hsc
  obtain ⟨C,hC,hspan⟩ := h T hT S hS hsc
  have hcard : (1 : ℝ) ≤ Nat.card G := by exact_mod_cast (Nat.card_pos (α := G))
  refine ⟨C,?_,hspan⟩
  have hp := Real.rpow_le_rpow_of_exponent_le hcard (show 1-eta' ≤ 1-eta by linarith)
  exact (mul_le_mul (mul_le_mul_of_nonneg_right hbb (Nat.cast_nonneg T)) hp
    (Real.rpow_nonneg (zero_le_one.trans hcard) _) (mul_nonneg hb (Nat.cast_nonneg T))).trans hC

end DirectedCycles
