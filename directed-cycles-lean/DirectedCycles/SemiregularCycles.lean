import DirectedCycles.SemiregularInduction

set_option autoImplicit false
universe u
namespace DirectedCycles

/-- Manuscript Theorem 3.7. The positive constant precedes every group,
graph and action; the conclusion is measured by the graph's vertex count. -/
theorem semiregular_nilpotent_cycle_theorem (r c Q : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ b : ℝ, 0 < b ∧
      ∀ (G V : Type u) [Group G] [Finite G] [Group.IsNilpotent G] [Finite V] [MulAction G V],
        ∀ X : Digraph V, (∀ g : G, ∀ x y, X (g • x) (g • y) ↔ X x y) →
        (∀ g : G, ∀ x : V, g • x = x → g = 1) → StronglyConnected X →
        Group.rank G ≤ r → Group.nilpotencyClass G ≤ c → 2 ≤ Nat.card V →
        Nat.card (Quotient (MulAction.orbitRel G V)) ≤ Q →
        ∃ L : Cycle X, b*(Nat.card V : ℝ)^(1-eps) ≤ L.length := by
  obtain ⟨b,hb,h⟩ := semiregular_group_bound.{u} r c Q eps heps
  have hQ : (0 : ℝ) < (Q : ℝ)+1 := by positivity
  refine ⟨b/((Q : ℝ)+1),div_pos hb hQ,?_⟩
  intro G V _ _ _ _ _ X hX hfree hsc hr hc hn hq
  obtain ⟨L,hL⟩ := h G V X hX hfree hsc hr hc hn hq
  refine ⟨L,?_⟩
  let q := Nat.card (Quotient (MulAction.orbitRel G V))
  have hcard : Nat.card V = Nat.card G*q := free_action_cardinality hfree
  have hqnat : 1 ≤ q := by
    by_contra he
    have hz : q = 0 := by omega
    rw [hz,mul_zero] at hcard
    omega
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqnat
  have hqQ : (q : ℝ) ≤ (Q : ℝ)+1 := by
    have hh : (q : ℝ) ≤ Q := by exact_mod_cast hq
    linarith
  have hp : (q : ℝ)^(1-eps) ≤ (Q : ℝ)+1 :=
    (Real.rpow_le_self_of_one_le hq1 (by linarith)).trans hqQ
  have hpow : (Nat.card V : ℝ)^(1-eps) ≤ ((Q : ℝ)+1)*(Nat.card G : ℝ)^(1-eps) := by
    rw [hcard,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp
      (Real.rpow_nonneg (Nat.cast_nonneg (Nat.card G)) (1-eps))
  calc
    b/((Q : ℝ)+1)*(Nat.card V : ℝ)^(1-eps) ≤
        b/((Q : ℝ)+1)*(((Q : ℝ)+1)*(Nat.card G : ℝ)^(1-eps)) :=
      mul_le_mul_of_nonneg_left hpow (div_nonneg hb.le hQ.le)
    _ = b*(Nat.card G : ℝ)^(1-eps) := by field_simp
    _ ≤ L.length := hL

end DirectedCycles
