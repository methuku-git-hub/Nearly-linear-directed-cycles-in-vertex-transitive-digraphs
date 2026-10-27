module

public import DirectedCycles.HaarEscapeBootstrap
public import DirectedCycles.CompactNSSWordWindow
public import DirectedCycles.HaarFiniteTrapping

@[expose] public section

set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]

/-- The escape-product estimate on a precompact NSS window. All Haar
normalizations and finite trapping scales are constructed here. -/
theorem locally_compact_escape_product {U : Set G} (hU : IsOpen U)
    (hU1 : (1 : G) ∈ U) (hUi : U⁻¹ = U) (hUc : IsCompact (closure U))
    (hnss : ∀ x : G, (∀ j : ℕ, x^j ∈ closure (U^4)) → x = 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ l : List G,
      escapeNorm U l.prod ≤ D*(l.map (escapeNorm U)).sum := by
  classical
  by_cases hproper : ∃ b : G, b ∉ U
  · let : MeasurableSpace G := borel G
    let : BorelSpace G := ⟨rfl⟩
    let μ := Measure.haar (G := G)
    have hfin : ∀ k : ℕ, μ (U^k) ≠ ⊤ := by
      intro k
      exact (lt_of_le_of_lt (measure_mono (Set.pow_subset_pow_left subset_closure))
        (compact_set_word_power hUc k).measure_lt_top).ne
    have hpos : 0 < μ.real U := ENNReal.toReal_pos (hU.measure_ne_zero μ ⟨1,hU1⟩)
      (by simpa only [pow_one] using hfin 1)
    obtain ⟨C,hC,hfirst0⟩ := compact_power_trapping (compact_closure_word_power hUc 4) hnss hU hU1
    have hfirst : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ U^4) → x ∈ U := by
      intro x hx
      apply hfirst0 x
      intro j hj
      by_cases hj0 : j = 0
      · simpa only [hj0,pow_zero] using subset_closure (Set.one_mem_pow hU1 : (1 : G) ∈ U^4)
      · exact subset_closure (hx j (by omega) hj)
    obtain ⟨N,hNlarge⟩ := exists_nat_gt (max 1 (4*(C : ℝ)*μ.real (U^3)/μ.real U))
    have hNposR : 0 < (N : ℝ) := zero_lt_one.trans ((le_max_left _ _).trans_lt hNlarge)
    have hN : 0 < N := by exact_mod_cast hNposR
    have hscale : 4*(C : ℝ)*μ.real (U^3) ≤ (N : ℝ)*μ.real U :=
      ((div_lt_iff₀ hpos).mp ((le_max_right _ _).trans_lt hNlarge)).le
    obtain ⟨S,P,hS,hS1,_hSi,hP1,hPi,hPN,hconj⟩ := compact_conjugate_word_window
      (compact_set_word_power hUc 3) hU hU1 (Set.one_mem_pow (subset_closure hU1)) N
    obtain ⟨M,hM,hsecond0⟩ := compact_power_trapping hUc (cyclic_nss_closure_of_fourth hU1 hnss) hS hS1
    have hsecond : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ M → x^j ∈ U) → x ∈ S := by
      intro x hx
      apply hsecond0 x
      intro j hj
      by_cases hj0 : j = 0
      · simpa only [hj0,pow_zero] using subset_closure hU1
      · exact subset_closure (hx j (by omega) hj)
    let D := 8*(C : ℝ)*(max 1 (μ.real (U^2)/μ.real U))*(M : ℝ)
    have hD : 0 < D := by
      have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
      have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
      have hK : 0 < max 1 (μ.real (U^2)/μ.real U) := zero_lt_one.trans_le (le_max_left _ _)
      exact mul_pos (mul_pos (mul_pos (by norm_num) hCr) hK) hMr
    refine ⟨D,hD,?_⟩
    apply escape_product_bound_of_regularized hU1 hD.le
    intro ε hε
    exact haar_escape_regularized μ hU hU1 hUi hproper hP1 hPi C M N hC hM hN
      hfirst hsecond (fun h hh y hy => hconj h hh y (Set.pow_subset_pow_left subset_closure hy))
      hPN (hfin 2) (hfin 3) hpos hscale hε
  · have hfull : ∀ x : G, x ∈ U := by simpa using hproper
    refine ⟨1,by norm_num,?_⟩
    intro l
    rw [(escapeNorm_eq_zero_iff hU1 l.prod).2 (fun j => hfull _)]
    exact mul_nonneg zero_le_one (List.sum_nonneg (by
      simpa using fun x (_ : x ∈ l) => escapeNorm_nonneg hU1 x))

/-- Every locally compact Hausdorff NSS group has an actual open
precompact escape window with a uniform product estimate. -/
theorem nss_escape_product_window (hnss : HasNoSmallSubgroups G) :
    ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ U⁻¹ = U ∧ IsCompact (closure U) ∧
      (∀ x : G, (∀ j : ℕ, x^j ∈ closure (U^4)) → x = 1) ∧
      ∃ D : ℝ, 0 < D ∧ ∀ l : List G,
        escapeNorm U l.prod ≤ D*(l.map (escapeNorm U)).sum := by
  obtain ⟨U,hU,hU1,hUi,hUc,hUnss⟩ := compact_nss_word_window hnss 4
  exact ⟨U,hU,hU1,hUi,hUc,hUnss,locally_compact_escape_product hU hU1 hUi hUc hUnss⟩
end DirectedCycles
