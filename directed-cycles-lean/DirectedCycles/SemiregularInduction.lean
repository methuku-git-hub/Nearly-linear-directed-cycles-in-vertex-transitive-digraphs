import DirectedCycles.LargeReturnBound
import DirectedCycles.SemiregularOrbitCycles
import DirectedCycles.SemiregularContraction
import DirectedCycles.SmallKernelLength

set_option autoImplicit false
universe u
namespace DirectedCycles

/-- The bounded-orbit estimate, temporarily measured against the acting
group order. The constant is uniform over all groups and actions. -/
def SemiregularGroupBound (r c Q : ℕ) (b eps : ℝ) : Prop :=
  ∀ (G V : Type u) [Group G] [Finite G] [Group.IsNilpotent G] [Finite V] [MulAction G V],
    ∀ X : Digraph V, (∀ g : G, ∀ x y, X (g • x) (g • y) ↔ X x y) →
    (∀ g : G, ∀ x : V, g • x = x → g = 1) → StronglyConnected X →
    Group.rank G ≤ r → Group.nilpotencyClass G ≤ c → 2 ≤ Nat.card V →
    Nat.card (Quotient (MulAction.orbitRel G V)) ≤ Q →
    ∃ L : Cycle X, b*(Nat.card G : ℝ)^(1-eps) ≤ L.length

/-- Orbit-count induction in Theorem 3.7. All branches use established
constructions; no smaller-orbit estimate remains a hypothesis. -/
theorem semiregular_group_bound (r c Q : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ b : ℝ, 0 < b ∧ SemiregularGroupBound.{u} r c Q b eps := by
  obtain ⟨bc,hbc,hcayley⟩ := nilpotent_cycle_theorem.{u} r c eps heps
  obtain ⟨bl,hbl,hlarge⟩ := large_return_cycle_bound.{u,u} r c eps heps
  induction Q with
  | zero =>
    refine ⟨1,by norm_num,?_⟩
    intro G V _ _ _ _ _ X _ hfree _ _ _ hn hq
    have hcard := free_action_cardinality hfree
    have hq0 : Nat.card (Quotient (MulAction.orbitRel G V)) = 0 := by omega
    rw [hq0,mul_zero] at hcard
    omega
  | succ Q ih =>
    obtain ⟨bp,hbp,hprev⟩ := ih
    let H := 8*((Q+1)+1)*((c+1)+1)
    let M := H^(c*∑ i ∈ Finset.range c,r^(i+1))
    have hMnat : 0 < M := pow_pos (by dsimp only [H]; positivity) _
    have hM : (0 : ℝ) < M := by exact_mod_cast hMnat
    let b := min 1 (min bc (min bl (bp/M)))
    have hb : 0 < b := lt_min (by norm_num) (lt_min hbc (lt_min hbl (div_pos hbp hM)))
    have hb1 : b ≤ 1 := min_le_left _ _
    have hbc' : b ≤ bc := (min_le_right _ _).trans (min_le_left _ _)
    have hbl' : b ≤ bl := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
    have hbpM : b ≤ bp/M := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
    have hbp' : b ≤ bp := hbpM.trans (div_le_self hbp.le (by exact_mod_cast hMnat))
    refine ⟨b,hb,?_⟩
    intro G V _ _ _ _ _ X hX hfree hsc hr hc hn hq
    have hGpos : (0 : ℝ) < Nat.card G := by exact_mod_cast (Nat.card_pos (α := G))
    have hpow : 0 ≤ (Nat.card G : ℝ)^(1-eps) := Real.rpow_nonneg hGpos.le _
    have weaken : ∀ d : ℝ, b ≤ d → (∃ L : Cycle X, d*(Nat.card G : ℝ)^(1-eps) ≤ L.length) →
        ∃ L : Cycle X, b*(Nat.card G : ℝ)^(1-eps) ≤ L.length := by
      rintro d hd ⟨L,hL⟩
      exact ⟨L,(mul_le_mul_of_nonneg_right hd hpow).trans hL⟩
    by_cases hqprev : Nat.card (Quotient (MulAction.orbitRel G V)) ≤ Q
    · exact weaken bp hbp' (hprev G V X hX hfree hsc hr hc hn hqprev)
    have hqeq : Nat.card (Quotient (MulAction.orbitRel G V)) = Q+1 := by omega
    let : Nontrivial V := finite_nontrivial_of_two_le_card hn
    rcases subsingleton_or_nontrivial G with hG | hG
    · let : Subsingleton G := hG
      obtain ⟨L⟩ := stronglyConnected_cycle hsc
      refine ⟨L,?_⟩
      rw [Nat.card_unique,Nat.cast_one,Real.one_rpow,mul_one]
      have hL : (2 : ℝ) ≤ L.length := by exact_mod_cast L.two_le
      linarith
    · let : Nontrivial G := hG
      by_cases hq1 : Nat.card (Quotient (MulAction.orbitRel G V)) = 1
      · obtain ⟨S,hS,f,hf⟩ := one_orbit_cayley_presentation X hX hfree hsc hq1
        obtain ⟨L,hL⟩ := (hcayley G hr hc).1 inferInstance S (cayley_stronglyConnected_generates S hS)
        exact weaken bc hbc' ⟨L.map f hf,hL⟩
      have hq2 : 2 ≤ Nat.card (Quotient (MulAction.orbitRel G V)) := by omega
      obtain ⟨a,⟨W⟩⟩ := semiregular_orbit_cycle_walk X hX hfree hsc hq2
      by_cases hK : elementClosure a = ⊤
      · obtain ⟨L,hL⟩ := semiregular_generating_voltage_cycle X hX hfree a W
          (elementClosure_eq_top_implies_cyclic a hK)
        refine ⟨L,?_⟩
        have hp := cardinal_rpow_le_card (G := G) eps heps.le
        have hlen : Nat.card G ≤ L.length := by rw [hL]; nlinarith [W.two_le]
        have hlen' : (Nat.card G : ℝ) ≤ L.length := by exact_mod_cast hlen
        exact (mul_le_mul_of_nonneg_right hb1 hpow).trans (by simpa only [one_mul] using hp.trans hlen')
      by_cases hsmall : orderOf (QuotientGroup.mk' (elementCommutators a) a) ≤ H
      · have hKcard : Nat.card (elementClosure a) ≤ M := by
          have hh := elementClosure_order_bound a r c hr hc
          rw [elementClosure_factor_card_eq_orderOf] at hh
          exact hh.trans (Nat.pow_le_pow_left hsmall _)
        obtain ⟨J,hF,Y,hY,hInv,hFree,hOrbits,hTwo,hLift⟩ := semiregular_cycle_reduction
          X hX hfree hsc a W (elementClosure a) (mem_elementClosure a) hK
        let : Finite J := hF
        let : MulAction (G ⧸ elementClosure a) ((G ⧸ elementClosure a) × J) :=
          coordinateMulAction (G ⧸ elementClosure a) J
        have hr' : Group.rank (G ⧸ elementClosure a) ≤ r :=
          (Group.rank_le_of_surjective (QuotientGroup.mk' (elementClosure a))
            (QuotientGroup.mk'_surjective (elementClosure a))).trans hr
        have hc' : Group.nilpotencyClass (G ⧸ elementClosure a) ≤ c :=
          (Group.nilpotencyClass_quotient_le (elementClosure a)).trans hc
        have hq' : Nat.card (Quotient (MulAction.orbitRel (G ⧸ elementClosure a)
            ((G ⧸ elementClosure a) × J))) ≤ Q := by rw [hOrbits,hqeq]; have := W.two_le; omega
        obtain ⟨L,hL⟩ := hprev (G ⧸ elementClosure a) ((G ⧸ elementClosure a) × J)
          Y hInv hFree hY hr' hc' hTwo hq'
        obtain ⟨L',hL'⟩ := hLift L
        apply weaken (bp/M) hbpM
        exact ⟨L',small_kernel_length (elementClosure a) bp M eps L.length L'.length hbp.le
          (by exact_mod_cast hKcard) heps.le hL (by exact_mod_cast hL')⟩
      · apply weaken bl hbl'
        apply hlarge G V X hX hfree hsc hr hc a W hK
        rw [hqeq]
        exact Nat.lt_of_not_ge hsmall

end DirectedCycles
