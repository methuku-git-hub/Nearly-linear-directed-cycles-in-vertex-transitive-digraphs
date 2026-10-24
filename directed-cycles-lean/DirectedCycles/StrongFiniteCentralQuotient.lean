import DirectedCycles.FiniteCentralQuotient
import DirectedCycles.StrongEscapeEstimates

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Actual strong finite NSS approximate groups admit a uniformly large
central local quotient. All analytic estimates, the least-escape element and
the first exit are derived; only the stated strong-group and NSS properties
are premises. -/
theorem strong_finite_central_quotient (K : ℕ) (hK : 1 ≤ K) :
    ∃ (J : ℕ) (d r : ℝ), 1 ≤ J ∧ 0 < d ∧ 0 < r ∧
      ∀ (G : Type*) [Group G] [Fintype G] [DecidableEq G] (A : Finset G),
      IsStrongFiniteApproximateGroup K A →
      (∀ g : G, escapeNorm A g = 0 → g = 1) → (∃ g ∈ A, g ≠ 1) →
      ∃ u ∈ A, u ≠ 1 ∧ ∃ N : ℕ, 0 < N ∧ u^N ∉ (A : Set G) ∧
        (∀ i < N, u^i ∈ (A : Set G)) ∧
        let W := escapeSublevel (A : Set G) r
        ∃ (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (V : Set G)
          (hP : LocalNormalSet (shortPowerProgression u N) V) (hW6 : W^6 ⊆ V) (T : Finset G),
          IsApproximateSubgroup (J : ℝ) (T : Set G) ∧
          d*A.card ≤ T.card ∧ (T : Set G)^200 ⊆ W ∧
          IsLocalFiniteApproximateGroup (hP.quotientAlgebra hW1 hWi hW6) (2*J)
            (hP.finiteWindowImage hW1 hWi hW6 T) ∧
          d*A.card ≤ (hP.finiteWindowImage hW1 hWi hW6 T).card * ((2*N-1 : ℕ) : ℝ) := by
  let B := 8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)
  let D := 2*(1000 : ℝ)^2*(K : ℝ)^11*B^2
  have hK0 : 0 < K := by omega
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨J,d,hJ,hd,hquot⟩ := finite_central_quotient (K : ℝ) (by exact_mod_cast hK) 1000 B D hB hD
  refine ⟨J,d,centralQuotientRadius 1000 B D,hJ,hd,centralQuotientRadius_pos 1000 hB hD,?_⟩
  intro G _ _ _ A hA hNSS hne
  obtain ⟨u,hu,hu1,hupos,hmin⟩ := exists_minimal_escape A hA.approximate.one_mem hNSS hne
  obtain ⟨N,hN,hexit,hprev⟩ := exists_first_escape hA.approximate.one_mem hupos
  refine ⟨u,hu,hu1,N,hN,hexit,hprev,?_⟩
  apply hquot G A hA.approximate ?_ (strong_approximate_product_all hA) u hupos hmin ?_ N hN hexit hprev
  · obtain ⟨S,hSi,hsmall,hfirst,hsecond⟩ := hA.trapping
    intro x hx
    apply hfirst x
    intro j hj hjC
    exact Set.pow_subset_pow_right hA.approximate.one_mem (by omega : 4 ≤ 100) (hx j hj hjC)
  · intro x hx
    have hx10 : x ∈ (A : Set G)^10 :=
      Set.subset_pow hA.approximate.one_mem (by omega : 10 ≠ 0) hx
    have hu10 : u ∈ (A : Set G)^10 :=
      Set.subset_pow hA.approximate.one_mem (by omega : 10 ≠ 0) hu
    exact strong_approximate_commutator_all hA hx10 hu10
end DirectedCycles
