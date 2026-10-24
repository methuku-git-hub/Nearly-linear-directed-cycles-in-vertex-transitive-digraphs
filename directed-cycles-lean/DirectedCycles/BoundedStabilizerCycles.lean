import DirectedCycles.SemiregularCycles
import DirectedCycles.StabilizerRemovalGraph

set_option autoImplicit false
universe u
namespace DirectedCycles

/-- A bounded stabilizer and a bounded-index nilpotent subgroup give a
uniform long-cycle estimate after a bounded loss in vertex count. -/
theorem bounded_stabilizer_cycle_bound (B r c Q : ℕ) (hBpos : 1 ≤ B)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ b : ℝ, 0 < b ∧ ∃ n₀ : ℕ, ∀ (G V : Type u) [Group G] [Fintype G] [Fintype V] [MulAction G V],
      ∀ X : Digraph V, (∀ g : G, ∀ x y, X (g • x) (g • y) ↔ X x y) →
      (∀ x y : V, ∃ g : G, g • x = y) → StronglyConnected X →
      ∀ N : Subgroup G, ∀ _hN : N.Normal, ∀ _hNil : Group.IsNilpotent N,
      Group.rank N ≤ r → Group.nilpotencyClass N ≤ c → N.index ≤ Q →
      (∀ x : V, Nat.card (MulAction.stabilizer G x) ≤ B) → n₀ ≤ Nat.card V →
      ∃ L : Cycle X, b*(Nat.card V : ℝ)^(1-eps) ≤ L.length := by
  obtain ⟨b,hb,hcycle⟩ := semiregular_nilpotent_cycle_theorem.{u} r c Q eps heps
  let M := B^(∑ i ∈ Finset.range c,(∑ j ∈ Finset.range c,r^(j+1))^(i+1))
  have hMnat : 0 < M := pow_pos (by omega) _
  have hM : (0 : ℝ) < M := by exact_mod_cast hMnat
  refine ⟨b/M,div_pos hb hM,2*M,?_⟩
  intro G V _ _ _ _ X hX ht hsc N hN hNil hr hc hIndex hStab hn
  let : N.Normal := hN
  let : Group.IsNilpotent N := hNil
  have hn2 : 2 ≤ Nat.card V := by nlinarith
  let : Nontrivial V := finite_nontrivial_of_two_le_card hn2
  let x : V := Classical.choice inferInstance
  obtain ⟨L,hL,hLN,hcardL,hr',hc',act,hfree,horb,hsize,hY,hInv,hLift⟩ :=
    stabilizer_removal_graph X hX ht hsc N x B r c hStab hr hc
  let : L.Normal := hL
  let YV := Quotient (MulAction.orbitRel L V)
  let K := N ⧸ L.comap N.subtype
  let : MulAction K YV := act
  let Y := QuotientDigraph X (Quotient.mk'' : V → YV)
  have hY2 : 2 ≤ Nat.card YV := by
    have hm : Nat.card L ≤ M := hcardL
    change Nat.card V ≤ Nat.card YV*Nat.card L at hsize
    nlinarith
  obtain ⟨C,hC⟩ := hcycle K YV Y hInv hfree hY hr' hc' hY2 (horb.trans hIndex)
  obtain ⟨C',hC'⟩ := hLift C
  refine ⟨C',?_⟩
  have hmul : (Nat.card V : ℝ) ≤ (Nat.card YV : ℝ)*M := by
    exact_mod_cast hsize.trans (Nat.mul_le_mul_left (Nat.card YV) hcardL)
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hMnat
  have hp : (Nat.card V : ℝ)^(1-eps) ≤ (Nat.card YV : ℝ)^(1-eps)*M := by
    calc
      (Nat.card V : ℝ)^(1-eps) ≤ ((Nat.card YV : ℝ)*M)^(1-eps) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hmul (by linarith)
      _ = (Nat.card YV : ℝ)^(1-eps)*(M : ℝ)^(1-eps) :=
        Real.mul_rpow (Nat.cast_nonneg _) hM.le
      _ ≤ (Nat.card YV : ℝ)^(1-eps)*M :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hm1 (by linarith))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc
    b/M*(Nat.card V : ℝ)^(1-eps) ≤ b/M*((Nat.card YV : ℝ)^(1-eps)*M) :=
      mul_le_mul_of_nonneg_left hp (div_nonneg hb.le hM.le)
    _ = b*(Nat.card YV : ℝ)^(1-eps) := by field_simp
    _ ≤ C.length := hC
    _ ≤ C'.length := by exact_mod_cast hC'

end DirectedCycles
