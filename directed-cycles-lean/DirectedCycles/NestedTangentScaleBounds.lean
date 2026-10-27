module

public import DirectedCycles.LieCurveCoordinateComparison
public import DirectedCycles.LocalNestedSegmentComparison

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Annulus bounds on two tangents on the same oriented ray bound the exact
ratio of their scales. -/
theorem nested_tangent_scale_bounds {v w : E} {t a b c d : ℝ}
    (ht : 0 ≤ t) (he : v = t • w) (hc : 0 < c)
    (hv : a ≤ ‖v‖ ∧ ‖v‖ ≤ b) (hw : c ≤ ‖w‖ ∧ ‖w‖ ≤ d) :
    a/d ≤ t ∧ t ≤ b/c := by
  have hn : ‖v‖ = t*‖w‖ := by rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
  have hd : 0 < d := hc.trans_le (hw.1.trans hw.2)
  constructor
  · apply (div_le_iff₀ hd).2
    have hmul := mul_le_mul_of_nonneg_left hw.2 ht
    nlinarith [hv.1]
  · apply (le_div_iff₀ hc).2
    have hmul := mul_le_mul_of_nonneg_left hw.1 ht
    nlinarith [hv.2]

/-- The small amount of slack in the exponential sandwich leaves room for
a uniform 1.1 comparison between the two inner escape times. -/
theorem nested_escape_scale_comparison {δ a₀ a₁ b₀ b₁ : ℝ}
    (hδ : 0 < δ) (ha₀ : 0 < a₀) (ha₁ : 0 < a₁)
    (hmin : a₁ ≤ a₀)
    (h₀ : (99/100)*δ < b₀/a₀)
    (h₁ : b₁/a₁ < (101/100)*δ) : b₁ < (11/10)*b₀ := by
  have h₀' := (lt_div_iff₀ ha₀).1 h₀
  have h₁' := (div_lt_iff₀ ha₁).1 h₁
  have hm := mul_le_mul_of_nonneg_left hmin (show 0 ≤ (101/100)*δ by positivity)
  have hp : 0 < δ*a₀ := mul_pos hδ ha₀
  nlinarith
end DirectedCycles
