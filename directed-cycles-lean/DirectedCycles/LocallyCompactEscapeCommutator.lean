import DirectedCycles.HaarEscapeCommutator
import DirectedCycles.LocallyCompactEscapeProduct

set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]

/-- Once an eighth-power NSS window and a product bound are given, all
inputs to the commutator estimate follow from local compactness and Haar measure. -/
theorem locally_compact_escape_commutator {U : Set G} (hU : IsOpen U)
    (hU1 : (1 : G) ∈ U) (hUi : U⁻¹ = U) (hUc : IsCompact (closure U))
    (hnss : ∀ x : G, (∀ j : ℕ, x^j ∈ closure (U^8)) → x = 1)
    {P : ℝ} (hP : 0 < P)
    (hp : ∀ l : List G, escapeNorm U l.prod ≤ P*(l.map (escapeNorm U)).sum) :
    ∃ B : ℝ, 0 < B ∧ ∀ g ∈ U, ∀ h ∈ U,
      escapeNorm U (g⁻¹*h⁻¹*g*h) ≤ B*escapeNorm U g*escapeNorm U h := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let μ := Measure.haar (G := G)
  have hfin : ∀ k : ℕ, μ (U^k) ≠ ⊤ := by
    intro k
    exact (lt_of_le_of_lt (measure_mono (Set.pow_subset_pow_left subset_closure))
      (compact_set_word_power hUc k).measure_lt_top).ne
  have hpos : 0 < μ.real U := ENNReal.toReal_pos (hU.measure_ne_zero μ ⟨1,hU1⟩)
    (by simpa only [pow_one] using hfin 1)
  obtain ⟨C,hC,hfirst0⟩ := compact_power_trapping (compact_closure_word_power hUc 8) hnss hU hU1
  have hfirst : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ U^8) → x ∈ U := by
    intro x hx
    apply hfirst0 x
    intro j hj
    by_cases hj0 : j = 0
    · simpa only [hj0,pow_zero] using subset_closure (Set.one_mem_pow hU1 : (1 : G) ∈ U^8)
    · exact subset_closure (hx j (by omega) hj)
  let B := max 1 (2*(C : ℝ)^2*P^2*μ.real (U^3)/μ.real U)
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨B,hB,?_⟩
  intro g hg h hh
  apply (haar_escape_commutator μ hU hU1 hUi C hC hfirst hP hp (hfin 2) (hfin 3) hpos hg hh).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (escapeNorm_nonneg hU1 g)) (escapeNorm_nonneg hU1 h)
end DirectedCycles
