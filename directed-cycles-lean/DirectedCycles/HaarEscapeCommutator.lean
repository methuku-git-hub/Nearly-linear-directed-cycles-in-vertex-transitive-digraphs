module

public import DirectedCycles.HaarNormalizedBump
public import DirectedCycles.MeasurableUnregularizedBump
public import DirectedCycles.BoundedDerivativeCommutator

@[expose] public section

set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]

/-- Haar convolution converts the proved escape-product inequality into
an actual commutator estimate on the original identity window. -/
theorem haar_escape_commutator {U : Set G} (hU : IsOpen U)
    (hU1 : (1 : G) ∈ U) (hUi : U⁻¹ = U)
    (C : ℕ) (hC : 0 < C)
    (hfirst : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ U^8) → x ∈ U)
    {P : ℝ} (hP : 0 < P)
    (hp : ∀ l : List G, escapeNorm U l.prod ≤ P*(l.map (escapeNorm U)).sum)
    (hfin2 : μ (U^2) ≠ ⊤) (hfin3 : μ (U^3) ≠ ⊤) (hpos : 0 < μ.real U)
    {g h : G} (hg : g ∈ U) (hh : h ∈ U) :
    escapeNorm U (g⁻¹*h⁻¹*g*h) ≤
      (2*(C : ℝ)^2*P^2*μ.real (U^3)/μ.real U)*escapeNorm U g*escapeNorm U h := by
  have hCr : 0 ≤ (C : ℝ) := Nat.cast_nonneg C
  have htrap4 : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ U^4) → x ∈ U := by
    intro x hx
    exact hfirst x (fun j hj hjC => Set.pow_subset_pow_right hU1 (by omega : 4 ≤ 8) (hx j hj hjC))
  have hconj : ∀ y ∈ U^3, ∀ z ∈ U, y⁻¹*z*y ∈ U^8 := by
    intro y hy z hz
    have hyi : y⁻¹ ∈ U^3 := by
      simpa only [← inv_pow,hUi] using Set.inv_mem_inv.mpr hy
    have hz1 : z ∈ U^1 := by simpa only [pow_one] using hz
    have h7 : y⁻¹*z*y ∈ U^7 := by
      have h := Set.mul_mem_mul (Set.mul_mem_mul hyi hz1) hy
      simpa only [← pow_add] using h
    exact Set.pow_subset_pow_right hU1 (by omega : 7 ≤ 8) h7
  have heconj : ∀ y ∈ U^3, ∀ z : G, escapeNorm U (y⁻¹*z*y) ≤ (C : ℝ)*escapeNorm U z :=
    fun y hy z => escapeNorm_conjugate_of_trapping hU1 C hC hfirst y (hconj y hy) z
  obtain ⟨φ,hφm,hφ,hφU,hφs,hφlip⟩ := measurable_unregularized_escape_bump hU hU1 hUi hP hp
  obtain ⟨hc,hf,hf1,hfs⟩ := haar_normalized_bump μ hU hUi hφm hφ hφU hφs hfin2 hpos
  let F := haarConvolution μ φ φ
  let f := fun x => F x/μ.real U
  have he : ∀ x, escapeNorm U x ≤ (C : ℝ)*boundedDerivative f x := by
    intro x
    exact (escapeNorm_le_mul_of_trapping (Set.one_mem_pow hU1) C hC htrap4 x).trans
      (mul_le_mul_of_nonneg_left (escapeNorm_le_boundedDerivative (Set.one_mem_pow hU1) hf hf1 hfs x) hCr)
  let R := (C : ℝ)*P^2*μ.real (U^3)/μ.real U
  have htwo : ∀ a ∈ U, ∀ b x : G,
      |groupDerivative b (groupDerivative a f) x| ≤ R*escapeNorm U a*escapeNorm U b := by
    intro a ha b x
    have hda : ∀ y, |groupDerivative a φ y| ≤ P*escapeNorm U a := hφlip a
    have hdb : ∀ y ∈ U^3, ∀ z,
        |groupDerivative (y⁻¹*b*y) φ z| ≤ P*((C : ℝ)*escapeNorm U b) := by
      intro y hy z
      exact (hφlip _ z).trans (mul_le_mul_of_nonneg_left (heconj y hy b) hP.le)
    have ht := haarConvolution_second_bound μ hc a b hfin3
      (mul_nonneg hP.le (escapeNorm_nonneg hU1 a))
      (mul_nonneg hP.le (mul_nonneg hCr (escapeNorm_nonneg hU1 b)))
      (fun y hy => groupDerivative_support_cube hU1 hφs ha hy) hda hdb x
    change |groupDerivative b (groupDerivative a (fun y => F y/μ.real U)) x| ≤ _
    rw [groupDerivative_div_constant,groupDerivative_div_constant,abs_div,abs_of_pos hpos]
    apply (div_le_div_of_nonneg_right ht hpos.le).trans_eq
    dsimp [R]
    ring
  have hc' := boundedDerivative_commutator_bound hf g h (htwo h hh g) (htwo g hg h)
  have hsum : boundedDerivative f (g⁻¹*h⁻¹*g*h) ≤ 2*R*escapeNorm U g*escapeNorm U h := by
    nlinarith
  exact (he _).trans ((mul_le_mul_of_nonneg_left hsum hCr).trans_eq (by dsimp [R]; ring))
end DirectedCycles
