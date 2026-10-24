import DirectedCycles.FiniteEscapeNeighbourhoods
import DirectedCycles.UniformCentralEscape
import DirectedCycles.LocalApproximateQuotient
import DirectedCycles.LocalQuotientCardinality
import DirectedCycles.ShortProgressionProperness

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Uniformly large finite approximate groups inside the actual first-exit
central quotient. The density is stated with the exact progression fibre
size; no global subgroup quotient is substituted. -/
theorem finite_central_quotient (K : ℝ) (hK : 1 ≤ K) (C : ℕ)
    (B D : ℝ) (hB : 0 < B) (hD : 0 ≤ D) :
    ∃ J : ℕ, ∃ d : ℝ, 1 ≤ J ∧ 0 < d ∧
      ∀ (G : Type*) [Group G] [DecidableEq G] (A : Finset G),
      IsApproximateSubgroup K (A : Set G) →
      (∀ x : G, (∀ k : ℕ, 1 ≤ k → k ≤ C → x^k ∈ (A : Set G)^4) → x ∈ A) →
      (∀ l : List G, escapeNorm A l.prod ≤ B*(l.map (escapeNorm A)).sum) →
      ∀ u : G, 0 < escapeNorm A u →
      (∀ v ∈ A, v ≠ 1 → escapeNorm A u ≤ escapeNorm A v) →
      (∀ x ∈ A, escapeNorm A (x⁻¹*u⁻¹*x*u) ≤ D*escapeNorm A x*escapeNorm A u) →
      ∀ N : ℕ, 0 < N → u^N ∉ A → (∀ i < N, u^i ∈ A) →
      let W := escapeSublevel (A : Set G) (centralQuotientRadius C B D)
      ∃ (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (V : Set G)
        (hP : LocalNormalSet (shortPowerProgression u N) V) (hW6 : W^6 ⊆ V) (T : Finset G),
        IsApproximateSubgroup (J : ℝ) (T : Set G) ∧
        d*A.card ≤ T.card ∧ (T : Set G)^200 ⊆ W ∧
        IsLocalFiniteApproximateGroup (hP.quotientAlgebra hW1 hWi hW6) (2*J)
          (hP.finiteWindowImage hW1 hWi hW6 T) ∧
        d*A.card ≤ (hP.finiteWindowImage hW1 hWi hW6 T).card * ((2*N-1 : ℕ) : ℝ) := by
  classical
  let r := centralQuotientRadius C B D
  have hr : 0 < r := centralQuotientRadius_pos C hB hD
  obtain ⟨L,d,hL,hd,hsmall⟩ := finite_escape_neighbourhoods K hK C 200 r hr
  let J := ⌈L⌉₊
  have hLJ : L ≤ (J : ℝ) := Nat.le_ceil L
  have hJ : 1 ≤ J := by exact_mod_cast hL.trans hLJ
  refine ⟨J,d,hJ,hd,?_⟩
  intro G _ _ A hA htrap hprod u hu hmin hcomm N hN hexit hprev
  let W := escapeSublevel (A : Set G) r
  have htrap2 : ∀ x : G, (∀ k : ℕ, 1 ≤ k → k ≤ C → x^k ∈ (A : Set G)^2) → x ∈ A := by
    intro x hx
    apply htrap x
    intro k hk hkC
    exact Set.pow_subset_pow_right hA.one_mem (by omega : 2 ≤ 4) (hx k hk hkC)
  obtain ⟨_,_,_,V,hP,hW6⟩ := uniform_central_quotient_window hA.one_mem hA.inv_eq_self C
    htrap2 hB hD hprod hu hmin hcomm hN hexit hprev
  have hW1 : (1 : G) ∈ W := one_mem_escapeSublevel hA.one_mem hr.le
  have hWi : W⁻¹ = W := escapeSublevel_symmetric hA.inv_eq_self r
  obtain ⟨T,hT,hTd,hTp⟩ := hsmall G A hA htrap
  have hTJ := hT.mono hLJ
  have hTW : (T : Set G) ⊆ W := (Set.subset_pow hT.one_mem (by omega : 200 ≠ 0)).trans hTp
  have hQ := global_approximate_window_quotient hP hW1 hWi hW6 hJ hTJ hTp
  have hcard := hP.finiteWindowImage_card_bound hW1 hWi hW6 T
    (shortPowerProgressionFinset u N) hTW (by rw [coe_shortPowerProgressionFinset])
  rw [card_shortPowerProgressionFinset hA.inv_eq_self C htrap2 u hN hexit hprev] at hcard
  refine ⟨hW1,hWi,V,hP,hW6,T,hTJ,hTd,hTp,hQ,?_⟩
  exact hTd.trans (by exact_mod_cast hcard)
end DirectedCycles
