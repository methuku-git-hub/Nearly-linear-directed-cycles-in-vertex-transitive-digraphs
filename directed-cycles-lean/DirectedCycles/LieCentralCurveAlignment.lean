module

public import DirectedCycles.LieCurveCoordinateComparison
public import DirectedCycles.NestedTangentScaleBounds

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- A first-exit endpoint in the central model segment determines the whole
curve and a quantitatively bounded signed coordinate. The coefficient is not
assumed positive; both possible orientations are retained. -/
theorem lie_central_curve_alignment {R r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hR : (1001/1000)*r < R)
    (hinj : Set.InjOn (lieExponential (G := G) (E := E)) (Metric.ball 0 R))
    (φ ψ : ℝ → G) (hφ0 : φ 0 = 1) (hψ0 : ψ 0 = 1)
    (hφc : ContinuousAt φ 0) (hψc : ContinuousAt ψ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (hψadd : ∀ s t : ℝ, ψ (s+t) = ψ s*ψ t)
    {X v : E}
    (hφX : HasDerivAt (fun t => chartAt E (1 : G) (φ t)-chartAt E (1 : G) 1) X 0)
    (hψv : HasDerivAt (fun t => chartAt E (1 : G) (ψ t)-chartAt E (1 : G) 1) v 0)
    (hX : r ≤ ‖X‖ ∧ ‖X‖ ≤ (1001/1000)*r)
    (hv : δ*r ≤ ‖v‖ ∧ ‖v‖ ≤ (1001/1000)*δ*r)
    (he : ψ 1 ∈ φ '' Set.Icc (-1 : ℝ) 1) :
    ∃ t : ℝ, (99/100)*δ < |t| ∧ |t| < (101/100)*δ ∧
      v = t • X ∧ ∀ s : ℝ, ψ s = φ (t*s) := by
  obtain ⟨t,ht,he⟩ := he
  have ht1 : |t| ≤ 1 := abs_le.mpr ht
  have hvR : ‖v‖ < R := by
    have hh := mul_le_mul_of_nonneg_right hδ1 (show 0 ≤ (1001/1000)*r by positivity)
    nlinarith [hv.2]
  have htX : |t| * ‖X‖ < R := by
    have hh := mul_le_mul_of_nonneg_right ht1 (norm_nonneg X)
    nlinarith [hX.2]
  obtain ⟨hvt,hagree⟩ := lie_curve_coordinate_comparison hinj ψ φ hψ0 hφ0 hψc hφc hψadd hφadd
    hψv hφX he.symm hvR htX
  have hnorm : ‖v‖ = ‖|t| • X‖ := by simp only [hvt,norm_smul,Real.norm_eq_abs,abs_abs]
  have hv' : δ*r ≤ ‖|t| • X‖ ∧ ‖|t| • X‖ ≤ (1001/1000)*δ*r := hnorm ▸ hv
  have hb := nested_tangent_scale_bounds (abs_nonneg t) (rfl : |t| • X = |t| • X) hr hv' hX
  have he₁ : δ*r/((1001/1000)*r) = (1000/1001)*δ := by field_simp
  have he₂ : ((1001/1000)*δ*r)/r = (1001/1000)*δ := by field_simp
  rw [he₁,he₂] at hb
  exact ⟨t,by nlinarith [hb.1],by nlinarith [hb.2],hvt,hagree⟩
end DirectedCycles
