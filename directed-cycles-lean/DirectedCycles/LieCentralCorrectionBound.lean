import DirectedCycles.LieExponentialCurve
import DirectedCycles.CentralLiftBoundedRounding

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ,E) ∞ G]

/-- Inversion on every constructed exponential line is exact. -/
theorem lieExponential_neg_line (v : E) (t : ℝ) :
    lieExponential (G := G) ((-t) • v) = (lieExponential (t • v))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← lieExponential_add_line,neg_add_cancel,zero_smul,lieExponential_zero]

/-- Signed rounding places the entire corrected model segment strictly
inside the inner exponential ball. The correction exponent is also bounded,
so its finite local power domains can be constructed. -/
theorem lie_central_correction_bound {r δ t t' M₀ M₁ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (ht : |t| ≤ (11/10)*δ)
    (ht'lo : (9/10)*δ ≤ t') (ht'hi : t' ≤ (11/10)*δ)
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (hratio : M₁ ≤ (11/10)*M₀)
    (v : E) (hv : ‖v‖ ≤ (1001/1000)*r) :
    ∃ m : ℤ, |(m : ℝ)| *M₁ ≤ 2*M₀ ∧
      ∀ n : ℝ, 0 ≤ n → n ≤ M₁ →
        lieExponential (G := G) ((t/M₁*n) • v) *
          (lieExponential (((m : ℝ)*t'/M₀*n) • v))⁻¹ ∈
            (lieExponential (G := G) (E := E)) '' Metric.ball (0 : E) (δ*r) := by
  obtain ⟨m,hm,hbound⟩ := central_lift_bounded_rounding hδ ht ht'lo ht'hi hM₀ hM₁ hratio
  refine ⟨m,hm,?_⟩
  intro n hn hnM
  let a := (t/M₁-(m : ℝ)*t'/M₀)*n
  have ha : |a| ≤ (121/200)*δ := hbound n hn hnM
  have hav : ‖a • v‖ < δ*r := by
    rw [norm_smul,Real.norm_eq_abs]
    have h₁ := mul_le_mul ha hv (norm_nonneg v) (show 0 ≤ (121/200)*δ by positivity)
    have hp : 0 < δ*r := mul_pos hδ hr
    nlinarith
  refine ⟨a • v,by simpa only [Metric.mem_ball,dist_zero_right] using hav,?_⟩
  rw [← lieExponential_neg_line,← lieExponential_add_line]
  congr 2
  dsimp only [a]
  ring
end DirectedCycles
