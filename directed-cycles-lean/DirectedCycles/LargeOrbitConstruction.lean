import DirectedCycles.SingleOrbitSampling
import DirectedCycles.PermutationImage
import DirectedCycles.ShortConnections
import DirectedCycles.LogarithmicBounds

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- The exact finite-size construction underlying the large-orbit theorem.
The degree assumption concerns the actual induced permutation group. -/
theorem large_normal_orbits_finite {G V : Type*} [Group G] [Fintype G]
    [Fintype V] [MulAction G V] (H : Subgroup G) [H.Normal]
    [Fintype (Quotient (MulAction.orbitRel H V))]
    [DecidableEq (Quotient (MulAction.orbitRel H V))]
    (D : Digraph V) (hconnected : Connected D)
    (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y)
    (hn : 2 ≤ Fintype.card V) (ell : ℝ) (hell : 0 ≤ ell) (B m : ℕ) (hB : 1 ≤ B)
    (hm : ∀ a : Quotient (MulAction.orbitRel H V), Fintype.card {x : V // Quotient.mk'' x = a} = m)
    (hm2 : 2 ≤ m)
    (hdiam : ∀ x y, MulAction.orbitRel H V x y →
      ∃ P : SimplePath (fun u v => D u v ∨ D v u) x y, (P.length : ℝ) ≤ (Fintype.card V : ℝ) ^ ell)
    (hlarge : 192 * degreeBudget (Fintype.card V) B * (connectionSize (Fintype.card V) ell) ^ 2 ≤ m) :
    letI := normalOrbitAction (V := V) H
    (∀ a : Quotient (MulAction.orbitRel H V),
      Fintype.card (MulAction.stabilizer (PermutationImage G (Quotient (MulAction.orbitRel H V))) a) ≤ B) →
    ∃ C : Cycle D, (Fintype.card V : ℝ) /
      (96 * (connectionSize (Fintype.card V) ell : ℝ) ^ 2) ≤ C.length := by
  let Ω := Quotient (MulAction.orbitRel H V)
  let π : V → Ω := Quotient.mk''
  let : MulAction G Ω := normalOrbitAction H
  intro hstab
  let n := Fintype.card V
  let ρ : ℝ := ⌈(n : ℝ) ^ ell⌉₊
  let u := ⌈4 * ρ * Real.log (2 * (n : ℝ))⌉₊
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hρ : 1 ≤ ρ := (Real.one_le_rpow hn1 hell).trans (Nat.le_ceil _)
  have hdiamρ : ∀ x y, MulAction.orbitRel H V x y →
      ∃ P : SimplePath (fun u v => D u v ∨ D v u) x y, (P.length : ℝ) ≤ ρ := by
    intro x y hxy
    obtain ⟨P, hP⟩ := hdiam x y hxy
    exact ⟨P, hP.trans (Nat.le_ceil _)⟩
  have hs : Function.Surjective π := Quotient.mk''_surjective
  have hπ : ∀ (g : G) x, π (g • x) = g • π x := normal_orbit_projection_smul H
  have htΩ := equivariant_quotient_transitive π hs hπ ht
  have hqn : Fintype.card Ω ≤ n := Fintype.card_le_of_surjective π hs
  have hnpos : 0 < Fintype.card V := by omega
  obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp hnpos
  have hqpos : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr ⟨π x₀⟩
  have hbudget : 1 ≤ degreeBudget n B := by unfold degreeBudget; nlinarith
  by_cases hq : Fintype.card Ω = 1
  · have hmn : m = n := by
      have h := card_eq_quotient_mul_fibre π m hm
      rw [hq, one_mul] at h
      exact h.symm
    have hl : 192 * (2 * u + 2) ^ 2 ≤ Fintype.card V := by
      have h : 192 * (connectionSize n ell) ^ 2 ≤
          192 * degreeBudget n B * (connectionSize n ell) ^ 2 := by
        exact Nat.mul_le_mul_right _ (by omega)
      exact (h.trans hlarge).trans hmn.le
    obtain ⟨C, hC⟩ := single_orbit_sampling_bound H D hD ht hn hq ρ hρ hdiamρ hl
    refine ⟨C, ?_⟩
    convert hC using 1
    simp only [connectionSize, ρ, n, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  · have hq2 : 2 ≤ Fintype.card Ω := by omega
    obtain ⟨Q, hQl, hQs, hQi, hshort⟩ := short_directed_connections H D hconnected hD ht hq2
      (fun a => by rw [hm]; exact hm2) ρ hρ hdiamρ
    obtain ⟨E, d, hEQ, hEl, hEi, hEs, hout, hin, hd, hdb⟩ :=
      sparse_subdigraph_of_induced_stabilizers Q hQl hQs hQi htΩ hq2 B (by
        intro a
        simpa only [Fintype.card_eq_nat_card] using hstab a)
    change d ≤ B * ⌈Real.log (Fintype.card Ω : ℝ) / Real.log 2⌉₊ at hdb
    have hdB : d ≤ degreeBudget n B := by
      have hlog : Real.log (Fintype.card Ω : ℝ) / Real.log 2 ≤ Real.log (n : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_right
          (Real.log_le_log (by exact_mod_cast hqpos) (by exact_mod_cast hqn))
          (Real.log_nonneg (by norm_num))
      have hc := Nat.ceil_mono hlog
      unfold degreeBudget
      exact hdb.trans (Nat.mul_le_mul_left B (hc.trans (Nat.le_add_right _ _)))
    have hld : 192 * d * (2 * u + 1 + 1) ^ 2 ≤ m := by
      calc 192 * d * (2 * u + 1 + 1) ^ 2 ≤ 192 * degreeBudget n B * (2 * u + 1 + 1) ^ 2 :=
             Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 192 hdB)
           _ = 192 * degreeBudget n B * (connectionSize n ell) ^ 2 := by
             simp only [connectionSize, u, ρ, Nat.add_assoc, Nat.reduceAdd]
           _ ≤ m := hlarge
    obtain ⟨C, hC⟩ := joining_short_connections H D hD ht hq2 m d (2 * u + 1) hm hld
      E hEl hEs hEi hout hin (fun a b hab => hshort a b (hEQ a b hab))
    refine ⟨C, ?_⟩
    convert hC using 1
    simp only [connectionSize, u, ρ, n, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring

end DirectedCycles
