import DirectedCycles.StrongEscapeEstimates
import DirectedCycles.MinimalEscapeWindow
import DirectedCycles.ShortProgressionProperness

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [Fintype G]

/-- The first central progression and its valid quotient window are constructed
from an actual nontrivial finite strong approximate group with NSS. Existence
of such strong groups and the later dimension drop are not asserted here. -/
theorem strong_nss_central_progression {K : ℕ} {A : Finset G}
    (hA : IsStrongFiniteApproximateGroup K A)
    (hNSS : ∀ g : G, escapeNorm A g = 0 → g = 1)
    (hne : ∃ g ∈ A, g ≠ 1) :
    ∃ u ∈ A, u ≠ 1 ∧ ∃ N : ℕ, 0 < N ∧ u^N ∉ (A : Set G) ∧
      (∀ i < N, u^i ∈ (A : Set G)) ∧
      (shortPowerProgressionFinset u N).card = 2*N-1 ∧
      shortPowerProgression u N ⊆ (A : Set G) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ (∀ x ∈ escapeSublevel A δ, Commute x u) ∧
        ∃ V : Set G, LocalNormalSet (shortPowerProgression u N) V ∧
          (escapeSublevel A δ)^6 ⊆ V := by
  obtain ⟨u,hu,hu1,huPos,hmin⟩ := exists_minimal_escape A hA.approximate.one_mem hNSS hne
  let B := 8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)
  let D := 2*(1000 : ℝ)^2*(K : ℝ)^11*B^2
  have hK : 0 < K := lt_of_lt_of_le (by omega : 0 < 1) hA.one_le
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨S,hSi,hsmall,hfirst,hsecond⟩ := hA.trapping
  have htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 → x^j ∈ (A : Set G)^2) → x ∈ (A : Set G) := by
    intro x hx
    apply hfirst
    intro j hj hjC
    exact (Set.pow_subset_pow_right hA.approximate.one_mem (by omega : 2 ≤ 100)) (hx j hj hjC)
  have hcomm : ∀ x ∈ (A : Set G),
      escapeNorm A (x⁻¹*u⁻¹*x*u) ≤ D*escapeNorm A x*escapeNorm A u := by
    intro x hx
    have hx10 : x ∈ (A : Set G)^10 := (Set.pow_subset_pow_right hA.approximate.one_mem
      (by omega : 1 ≤ 10)) (by simpa using hx)
    have hu10 : u ∈ (A : Set G)^10 := (Set.pow_subset_pow_right hA.approximate.one_mem
      (by omega : 1 ≤ 10)) (by simpa using hu)
    exact strong_approximate_commutator_all hA hx10 hu10
  obtain ⟨N,hN,hexit,hprev,δ,hδ,hδhalf,hcentral,V,hV,hpow⟩ :=
    minimal_escape_quotient_window hA.approximate.one_mem hA.approximate.inv_eq_self 1000 htrap
      hB hD (strong_approximate_product_all hA) huPos hmin hcomm
  refine ⟨u,hu,hu1,N,hN,hexit,hprev,?_,?_,δ,hδ,hδhalf,hcentral,V,hV,hpow⟩
  · exact card_shortPowerProgressionFinset hA.approximate.inv_eq_self 1000 htrap u hN hexit hprev
  · exact shortPowerProgression_subset hA.approximate.inv_eq_self u N hprev
end DirectedCycles
