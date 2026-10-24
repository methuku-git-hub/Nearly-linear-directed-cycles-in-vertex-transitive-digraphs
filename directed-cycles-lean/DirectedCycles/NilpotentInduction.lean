import DirectedCycles.CayleyInductionStep
import DirectedCycles.LayerInductionStep

set_option autoImplicit false
universe u
namespace DirectedCycles

/-- The simultaneous nilpotency-class induction, with uniform rank-dependent
constants and a fixed spanning cutoff independent of the requested error. -/
theorem nilpotent_spanning_bounds (c r n : ℕ) (hcn : c ≤ n) (eps : ℝ) (heps : 0 < eps) :
    ∃ b : ℝ, 0 < b ∧ ∀ (G : Type u) [Group G] [Finite G] [Group.IsNilpotent G],
      Group.rank G ≤ r → Group.nilpotencyClass G ≤ c →
      CayleySpanningBound G (n+1) b eps ∧ LayerSpanningBound G (n+1) b eps := by
  induction c using Nat.strong_induction_on generalizing r n eps with
  | h c ih =>
    by_cases hc1 : c ≤ 1
    · refine ⟨abelianLayerConstant r (n+1),(abelianLayerConstant_bounds r (n+1)).1,?_⟩
      intro G _ _ _ hr hc
      let : CommGroup G := commGroupOfNilpotencyClass (hc.trans hc1)
      exact abelian_spanning_bounds r (n+1) hr eps heps.le
    · have hd : c/2 < c := by omega
      have hdn : c/2 ≤ n := (Nat.div_le_self c 2).trans hcn
      have hlower : ∀ eta : ℝ, 0 < eta → ∃ b : ℝ, 0 < b ∧
          ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H],
            Group.rank H ≤ ∑ i ∈ Finset.range c,r^(i+1) →
            Group.nilpotencyClass H ≤ c/2 → LayerSpanningBound H (n+1) b eta := by
        intro eta heta
        obtain ⟨b,hb,hbounds⟩ := ih (c/2) hd (∑ i ∈ Finset.range c,r^(i+1)) n hdn eta heta
        exact ⟨b,hb,fun H _ _ _ hr hc => (hbounds H hr hc).2⟩
      have hcurrent : ∀ eta : ℝ, 0 < eta → ∃ b : ℝ, 0 < b ∧
          ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H],
            Group.rank H ≤ r → Group.nilpotencyClass H ≤ c → CayleySpanningBound H (n+1) b eta :=
        cayley_bound_from_lower_classes r c n hcn hlower
      obtain ⟨bq,hbq,hq⟩ := hcurrent eps heps
      obtain ⟨bl,hbl,hl⟩ := layer_bound_from_cayley_and_lower r c n hcn hcurrent hlower eps heps
      refine ⟨min bq bl,lt_min hbq hbl,?_⟩
      intro G _ _ _ hr hc
      exact ⟨(hq G hr hc).weaken hbq.le (min_le_left _ _) le_rfl,
        (hl G hr hc).weaken hbl.le (min_le_right _ _) le_rfl⟩

end DirectedCycles
