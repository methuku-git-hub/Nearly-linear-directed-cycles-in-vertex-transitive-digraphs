import DirectedCycles.LocalRelationCurveCoordinates
import DirectedCycles.LocalRelationCurveGermUniqueness
import DirectedCycles.LocalMultiplicativeCurveSmooth

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]

/-- Every actual smooth identity coordinate law detects a nonzero tangent of
an actual nontrivial local curve. This keeps the chart used for the subsequent
product-coordinate construction fixed. -/
theorem local_curve_coordinate_nonzero_tangent (Q : LocalGroupAlgebra H)
    (a : OpenPartialHomeomorph E H) (ha0 : (0 : E) ∈ a.source) (ha1 : a 0 = Q.one)
    (μ : E × E → E) (hμ0 : μ (0,0) = 0) (hμ : ContDiffAt ℝ ∞ μ (0,0))
    (hrel : ∀ᶠ p : E × E in 𝓝 (0,0), Q.mulRel (a p.1) (a p.2) (a (μ p)))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id)
    (f : ℝ → H) (hf0 : f 0 = Q.one) (hfc : ContinuousAt f 0)
    (hflaw : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t)))
    (hf1 : f 1 ≠ Q.one) :
    ContDiffAt ℝ ∞ (fun t => a.symm (f t)) 0 ∧
      ∃ v : E, v ≠ 0 ∧ HasDerivAt (fun t => a.symm (f t)) v 0 := by
  obtain ⟨hg0,hgc,s,hs,hglaw⟩ := local_relation_curve_coordinate_law Q a ha0 ha1 μ hμ0 hμ.continuousAt
    hrel f hf0 hfc (by norm_num : (0 : ℝ)<1) hflaw
  let g : ℝ → E := fun t => a.symm (f t)
  obtain ⟨v,hv⟩ := local_multiplicative_curve_hasDerivAt μ (hμ.of_le (by simp)) hl hr
    g hg0 hgc hs hglaw
  have hgSmooth := local_multiplicative_curve_contDiffAt μ hμ hl hr g hg0 hgc hs hglaw
  have hfT : Filter.Tendsto f (𝓝 0) (𝓝 Q.one) := by simpa only [hf0] using hfc.tendsto
  have ht : Q.one ∈ a.target := ha1 ▸ a.mapsTo ha0
  have hfnear : ∀ᶠ t : ℝ in 𝓝 0, f t ∈ a.target := hfT.eventually (a.open_target.mem_nhds ht)
  have heq : f =ᶠ[𝓝 (0 : ℝ)] (fun t => a (g t)) := by
    filter_upwards [hfnear] with t ht
    exact (a.right_inv ht).symm
  refine ⟨hgSmooth,v,?_,hv⟩
  intro hv0
  have hgv : HasDerivAt g 0 0 := hv0 ▸ hv
  have hconst : HasDerivAt (fun _ : ℝ => (0 : E)) 0 0 := hasDerivAt_const 0 0
  have hgeq : g =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : E)) :=
    local_multiplicative_curve_eventually_unique μ (hμ.of_le (by simp)) g (fun _ => 0)
      hg0 rfl hgv hconst hs (by norm_num : (0 : ℝ)<1) hglaw (fun _ _ _ => hμ0.symm)
  have hone : f =ᶠ[𝓝 (0 : ℝ)] (fun _ => Q.one) := by
    filter_upwards [heq,hgeq] with t he hg
    rw [he,hg,ha1]
  apply hf1
  exact local_relation_curve_eq_of_eventually_eq Q f (fun _ => Q.one) hf0 hflaw
    (r := 1) (s := 1) (fun _ _ _ => Q.one_mul Q.one) hone 1 (by norm_num) (by norm_num)
end DirectedCycles
