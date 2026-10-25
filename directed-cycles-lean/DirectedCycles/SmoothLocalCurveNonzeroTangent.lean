module

public import DirectedCycles.LocalRelationCurveCoordinates
public import DirectedCycles.LocalRelationCurveGermUniqueness
public import DirectedCycles.LocalMultiplicativeCurveSmooth

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [ChartedSpace E H] [IsManifold 𝓘(ℝ,E) ∞ H]

/-- A nontrivial continuous local relation curve in a smooth local group has
a nonzero actual coordinate tangent. Smoothness and nonvanishing follow from
the local law and ODE uniqueness, without a global curve or ambient group. -/
theorem smooth_local_curve_nonzero_tangent (Q : LocalGroupAlgebra H)
    (hQ : LocalGroupSmoothness (E := E) Q) (f : ℝ → H)
    (hf0 : f 0 = Q.one) (hfc : ContinuousAt f 0)
    (hflaw : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t)))
    (hf1 : f 1 ≠ Q.one) :
    ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ f 0 ∧
      ∃ a : OpenPartialHomeomorph E H, (0 : E) ∈ a.source ∧ a 0 = Q.one ∧
        ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a 0 ∧
        ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a.symm Q.one ∧
        ∃ v : E, v ≠ 0 ∧ HasDerivAt (fun t => a.symm (f t)) v 0 := by
  obtain ⟨a,ha0,ha1,haSmooth,hbSmooth,μ,hμ0,hμ,hrel,hl,hr,_⟩ := smooth_local_identity_coordinates Q hQ
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
  have hfs : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ f 0 := by
    have hh : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ (fun t => a (g t)) 0 :=
      haSmooth.comp_of_eq hgSmooth.contMDiffAt hg0
    exact hh.congr_of_eventuallyEq heq
  refine ⟨hfs,a,ha0,ha1,haSmooth,hbSmooth,v,?_,hv⟩
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
