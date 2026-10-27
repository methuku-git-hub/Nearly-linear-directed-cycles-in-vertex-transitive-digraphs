module

public import DirectedCycles.WordBallBump
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- A measurable word-window bump obtained by averaging indicators of
successive word translates. This avoids assuming the word set is finite. -/
noncomputable def wordWindowBump (Q U : Set G) (N : ℕ) (x : G) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, (Q^j*U).indicator (fun _ => (1 : ℝ)) x

omit [Group G] in
/-- Indicator bounds used in the actual finite average. -/
theorem one_indicator_bounds (A : Set G) (x : G) :
    0 ≤ A.indicator (fun _ => (1 : ℝ)) x ∧ A.indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
  classical
  by_cases hx : x ∈ A <;> simp [Set.indicator,hx]

/-- The bump lies between zero and one. -/
theorem wordWindowBump_bounds (Q U : Set G) {N : ℕ} (hN : 0 < N) (x : G) :
    0 ≤ wordWindowBump Q U N x ∧ wordWindowBump Q U N x ≤ 1 := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hn.le)
      (Finset.sum_nonneg (fun j _ => (one_indicator_bounds (Q^j*U) x).1))
  · have hs : (∑ j ∈ Finset.range N, (Q^j*U).indicator (fun _ => (1 : ℝ)) x) ≤ N := by
      calc
        _ ≤ ∑ _j ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_le_sum (fun j _ => (one_indicator_bounds (Q^j*U) x).2)
        _ = N := by simp
    change (N : ℝ)⁻¹ * _ ≤ 1
    calc
      _ ≤ (N : ℝ)⁻¹ * N := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn.le)
      _ = 1 := inv_mul_cancel₀ hn.ne'

/-- The original open window is a plateau of height one. -/
theorem wordWindowBump_eq_one {Q U : Set G} (hQ : (1 : G) ∈ Q)
    {N : ℕ} (hN : 0 < N) {x : G} (hx : x ∈ U) : wordWindowBump Q U N x = 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hm : ∀ j : ℕ, x ∈ Q^j*U := fun j =>
    ⟨1,Set.one_mem_pow hQ, x,hx,one_mul x⟩
  simp [wordWindowBump,Set.indicator_of_mem (hm _),hn]

/-- The bump has the same second-power support used in the finite
trapping convolution, with no topological assumption on the generators. -/
theorem wordWindowBump_support {Q U : Set G} (hQ : (1 : G) ∈ Q)
    {N : ℕ} (hQU : Q^N ⊆ U) {x : G} (hx : x ∉ U^2) : wordWindowBump Q U N x = 0 := by
  have hm : ∀ j ∈ Finset.range N, x ∉ Q^j*U := by
    intro j hj hxj
    have hpow : Q^j ⊆ Q^N := Set.pow_subset_pow_right hQ (Nat.le_of_lt (Finset.mem_range.mp hj))
    have hu : Q^j*U ⊆ U*U := Set.mul_subset_mul (hpow.trans hQU) Set.Subset.rfl
    exact hx (by simpa only [pow_two] using hu hxj)
  have hz : (∑ j ∈ Finset.range N, (Q^j*U).indicator (fun _ => (1 : ℝ)) x) = 0 :=
    Finset.sum_eq_zero (fun j hj => Set.indicator_of_notMem (hm j hj) _)
  rw [wordWindowBump,hz,mul_zero]

/-- Translation by one generator shifts the indicator sum by at most
one term, giving the quantitative Lipschitz estimate after normalization. -/
theorem wordWindowBump_translation_le {Q U : Set G} {q : G} (hq : q ∈ Q)
    {N : ℕ} (hN : 0 < N) (x : G) :
    wordWindowBump Q U N x ≤ wordWindowBump Q U N (q*x) + 1/(N : ℝ) := by
  classical
  let a : ℕ → ℝ := fun j => (Q^j*U).indicator (fun _ => (1 : ℝ)) (q*x)
  have hi : ∀ j : ℕ, (Q^j*U).indicator (fun _ => (1 : ℝ)) x ≤ a (j+1) := by
    intro j
    by_cases hx : x ∈ Q^j*U
    · have hqx : q*x ∈ Q^(j+1)*U := by
        rcases hx with ⟨w,hw,u,hu,rfl⟩
        refine ⟨q*w,?_,u,hu,mul_assoc q w u⟩
        rw [pow_succ']
        exact Set.mul_mem_mul hq hw
      simp only [Set.indicator_of_mem hx,a,Set.indicator_of_mem hqx,le_refl]
    · rw [Set.indicator_of_notMem hx]
      exact (one_indicator_bounds _ _).1
  have hsum : (∑ j ∈ Finset.range N, a (j+1)) ≤ (∑ j ∈ Finset.range N, a j)+1 := by
    have he : (∑ j ∈ Finset.range N, a (j+1)) + a 0 =
        (∑ j ∈ Finset.range N, a j)+a N := by
      clear hN
      induction N with
      | zero => simp
      | succ n ih => simp only [Finset.sum_range_succ]; linarith
    have ha := (one_indicator_bounds (Q^0*U) (q*x)).1
    have hb := (one_indicator_bounds (Q^N*U) (q*x)).2
    change 0 ≤ a 0 at ha
    change a N ≤ 1 at hb
    linarith
  have htotal := (Finset.sum_le_sum (fun j (_ : j ∈ Finset.range N) => hi j)).trans hsum
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hscaled := mul_le_mul_of_nonneg_left htotal (inv_nonneg.mpr hn.le)
  simpa only [wordWindowBump,a,mul_add,mul_one,one_div] using hscaled

/-- Symmetry of the generator set gives a two-sided derivative bound. -/
theorem wordWindowBump_derivative {Q U : Set G} (hQi : Q⁻¹ = Q)
    {q : G} (hq : q ∈ Q) {N : ℕ} (hN : 0 < N) (x : G) :
    |wordWindowBump Q U N (q⁻¹*x)-wordWindowBump Q U N x| ≤ 1/(N : ℝ) := by
  have hqi : q⁻¹ ∈ Q := by simpa only [hQi] using Set.inv_mem_inv.mpr hq
  have h₁ := wordWindowBump_translation_le (U := U) hqi hN x
  have h₂ := wordWindowBump_translation_le (U := U) hq hN (q⁻¹*x)
  simp only [mul_inv_cancel_left] at h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Openness of the base window suffices for measurability of every
term, even if the arbitrary generator set is not measurable. -/
theorem wordWindowBump_measurable [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Q U : Set G) (hU : IsOpen U) (N : ℕ) :
    Measurable (wordWindowBump Q U N) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.indicator hU.mul_left.measurableSet
end DirectedCycles
