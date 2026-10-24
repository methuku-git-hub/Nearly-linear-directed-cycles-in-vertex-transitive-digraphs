import DirectedCycles.LieCurveSmoothProductCoordinates
import DirectedCycles.LieOneParameterSmooth
import DirectedCycles.LieOneParameterNonzero
import DirectedCycles.VectorComplementDimension

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E G] [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- The actual nontrivial continuous one-parameter curve has product coordinates
which are smooth in both directions on their whole domains, with transverse
dimension one less. -/
theorem lieGroup_one_parameter_smooth_coordinates
    (φ : ℝ → G) (hφ0 : φ 0 = 1) (hφcont : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (hnt : ∃ t : ℝ, φ t ≠ 1) :
    ∃ (v : E) (ℓ : E →L[ℝ] ℝ), v ≠ 0 ∧ ℓ v = 1 ∧
      Module.finrank ℝ ℓ.ker + 1 = Module.finrank ℝ E ∧
      ∃ a : OpenPartialHomeomorph (ℝ × ℓ.ker) G,
        (0 : ℝ × ℓ.ker) ∈ a.source ∧ a 0 = 1 ∧
        ContMDiffOn 𝓘(ℝ,ℝ × ℓ.ker) 𝓘(ℝ,E) ∞ a a.source ∧
        ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ × ℓ.ker) ∞ a.symm a.target ∧
        ∀ᶠ p : ℝ × ℓ.ker in 𝓝 (0 : ℝ × ℓ.ker),
          a p = φ p.1*(chartAt E (1 : G)).symm ((p.2 : E)+(chartAt E (1 : G)) 1) := by
  have hφ := lieGroup_one_parameter_contMDiff (E := E) φ hφ0 hφcont hφadd
  obtain ⟨v,hv0,hv⟩ := lieGroup_one_parameter_nonzero_derivative (E := E) φ hφ0 hφcont hφadd hnt
  obtain ⟨ℓ,hℓ⟩ := exists_continuous_dual_eq_one v hv0
  let A := vectorComplementEquiv v ℓ hℓ
  have hA : ∀ t : ℝ, A (t,0) = t • v := by
    intro t
    simp only [A,vectorComplementEquiv_apply,ZeroMemClass.coe_zero,add_zero]
  obtain ⟨a,ha0,ha1,haSmooth,haInv,hformula⟩ := lie_curve_smooth_product_coordinates φ hφ0 hφ hv A hA
  refine ⟨v,ℓ,hv0,hℓ,vectorComplement_dimension v ℓ hℓ,a,ha0,ha1,haSmooth,haInv,?_⟩
  simpa only [A,vectorComplementEquiv_apply,zero_smul,zero_add] using hformula
end DirectedCycles
