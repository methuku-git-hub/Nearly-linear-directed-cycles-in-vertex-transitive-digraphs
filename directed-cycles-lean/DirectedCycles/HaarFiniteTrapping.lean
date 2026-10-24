import DirectedCycles.HaarFiniteTrappingCore
import DirectedCycles.CompactConjugateWordWindow
import Mathlib.MeasureTheory.Measure.Haar.Basic

set_option autoImplicit false
open MeasureTheory
open scoped Topology Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Compactness of actual set word powers. -/
theorem compact_set_word_power {K : Set G} (hK : IsCompact K) (n : ℕ) : IsCompact (K^n) := by
  induction n with
  | zero => change IsCompact ({1} : Set G); exact isCompact_singleton
  | succ n ih => rw [pow_succ]; exact ih.mul hK

/-- Finite trapping for a symmetric precompact identity neighbourhood.
The scale and both measurable convolution bumps are chosen uniformly
before the arbitrary symmetric generator set and its word radius. -/
theorem haar_finite_trapping [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    {U : Set G} (hU : IsOpen U) (hU1 : (1 : G) ∈ U) (hUi : U⁻¹ = U)
    (hcompact : IsCompact (closure U)) (m : ℕ) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ V⁻¹ = V ∧
      ∀ Q : Set G, (1 : G) ∈ Q → Q⁻¹ = Q →
        (∀ q ∈ Q, ∀ j : ℕ, q^j ∈ V) →
        ∀ n : ℕ, 0 < n → Q^n ⊆ U → Q^(m*n) ⊆ U^4 := by
  have hfin : ∀ r : ℕ, μ (U^r) ≠ ⊤ := by
    intro r
    exact (lt_of_le_of_lt (measure_mono (Set.pow_subset_pow_left subset_closure))
      (compact_set_word_power hcompact r).measure_lt_top).ne
  have hpos : 0 < μ.real U := by
    apply ENNReal.toReal_pos (hU.measure_ne_zero μ ⟨1,hU1⟩)
    simpa only [pow_one] using hfin 1
  obtain ⟨M,hM⟩ := exists_nat_gt (max 1 ((m : ℝ)*(μ.real (U^2)+μ.real (U^3))/μ.real U))
  have hMR : (1 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hMn : 0 < M := by exact_mod_cast (zero_lt_one.trans hMR)
  have hscale : (m : ℝ)*(μ.real (U^2)+μ.real (U^3)) < (M : ℝ)*μ.real U :=
    (div_lt_iff₀ hpos).mp ((le_max_right _ _).trans_lt hM)
  let K := (closure U)^3
  have hK : IsCompact K := compact_set_word_power hcompact 3
  have hK1 : (1 : G) ∈ K := Set.one_mem_pow (subset_closure hU1)
  obtain ⟨V,P,hV,hV1,hVi,hP1,hPi,hPM,hconj⟩ := compact_conjugate_word_window hK hU hU1 hK1 M
  refine ⟨V,hV,hV1,hVi,?_⟩
  intro Q hQ1 hQi hcyclic n hn hQn
  exact haar_finite_trapping_core μ hQ1 hP1 hU1 hQi hPi hUi hU hn hMn hQn hPM hcyclic
    (fun v hv y hy => hconj v hv y (Set.pow_subset_pow_left subset_closure hy))
    (hfin 2) (hfin 3) hscale

/-- The finite-trapping input for every locally compact Hausdorff group,
with Haar measure supplied by the library's construction. No measure or
analytic estimate is left as an additional structural assumption. -/
theorem locally_compact_finite_trapping [T2Space G] [LocallyCompactSpace G]
    {U : Set G} (hU : IsOpen U) (hU1 : (1 : G) ∈ U) (hUi : U⁻¹ = U)
    (hcompact : IsCompact (closure U)) (m : ℕ) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ V⁻¹ = V ∧
      ∀ Q : Set G, (1 : G) ∈ Q → Q⁻¹ = Q →
        (∀ q ∈ Q, ∀ j : ℕ, q^j ∈ V) →
        ∀ n : ℕ, 0 < n → Q^n ⊆ U → Q^(m*n) ⊆ U^4 := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  exact haar_finite_trapping Measure.haar hU hU1 hUi hcompact m
end DirectedCycles
