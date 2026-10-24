import DirectedCycles.SmoothLocalIdentityChart
import DirectedCycles.SmoothLocalCoordinateDomain
import DirectedCycles.LocalCurveCoordinateNonzeroTangent
import DirectedCycles.SmoothLocalCurveRegularity
import DirectedCycles.LocalCurveSmoothProductMap
import DirectedCycles.VectorComplementDimension

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E H] [IsManifold 𝓘(ℝ,E) ∞ H]

/-- A nontrivial actual local curve constructs smooth product coordinates
with transverse dimension exactly one less. Smoothness holds on the entire
chosen chart source and target, without a global ambient Lie group. -/
theorem smooth_local_curve_product_coordinates (Q : LocalGroupAlgebra H)
    (hQ : LocalGroupSmoothness (E := E) Q) (f : ℝ → H) (hf0 : f 0 = Q.one)
    (hfc : ContinuousAt f 0)
    (hadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t)))
    (hf1 : f 1 ≠ Q.one) :
    ∃ (v : E) (ℓ : E →L[ℝ] ℝ), v ≠ 0 ∧ ℓ v = 1 ∧
      Module.finrank ℝ ℓ.ker+1 = Module.finrank ℝ E ∧
      ∃ (b : OpenPartialHomeomorph (ℝ × ℓ.ker) H) (σ : ℓ.ker → H),
        (0 : ℝ × ℓ.ker) ∈ b.source ∧ b 0 = Q.one ∧ σ 0 = Q.one ∧
        ContMDiffOn 𝓘(ℝ,ℝ × ℓ.ker) 𝓘(ℝ,E) ∞ b b.source ∧
        ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ × ℓ.ker) ∞ b.symm b.target ∧
        ∀ᶠ p : ℝ × ℓ.ker in 𝓝 0, Q.mulRel (f p.1) (σ p.2) (b p) := by
  obtain ⟨a,ha0,ha1,ha,hai⟩ := smooth_identity_chart (E := E) Q.one
  obtain ⟨μ,S,hSo,hS0,hμ0,hμ,hrel,hl,hr,_⟩ := smooth_local_coordinate_domain Q hQ a ha0 ha1 ha hai
  have hμAt := hμ.contDiffAt (hSo.mem_nhds hS0)
  have hrelNear : ∀ᶠ p : E × E in 𝓝 (0,0), Q.mulRel (a p.1) (a p.2) (a (μ p)) := by
    filter_upwards [hSo.mem_nhds hS0] with p hp
    exact hrel p hp
  obtain ⟨hgSmooth,v,hv0,hv⟩ := local_curve_coordinate_nonzero_tangent Q a ha0 ha1 μ hμ0 hμAt hrelNear hl hr f hf0 hfc hadd hf1
  let g : ℝ → E := fun t => a.symm (f t)
  have hg0 : g 0 = 0 := by dsimp only [g]; rw [hf0,← ha1]; exact a.left_inv ha0
  have htarget : Q.one ∈ a.target := ha1 ▸ a.mapsTo ha0
  have hfT : Filter.Tendsto f (𝓝 0) (𝓝 Q.one) := by simpa only [hf0] using hfc.tendsto
  have heq : f =ᶠ[𝓝 (0 : ℝ)] (fun t => a (g t)) := by
    filter_upwards [hfT.eventually (a.open_target.mem_nhds htarget)] with t ht
    exact (a.right_inv ht).symm
  have hfSmooth : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ f 0 :=
    ((ha.contMDiffAt (a.open_source.mem_nhds ha0)).comp_of_eq hgSmooth.contMDiffAt hg0).congr_of_eventuallyEq heq
  let T : Set ℝ := {t | |t| < 1 ∧ f t ∈ a.target}
  have hT0 : 0 ∈ T := ⟨by norm_num,by rw [hf0]; exact htarget⟩
  have hfAt : ∀ t ∈ T, ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ f t :=
    fun _ ht => smooth_local_curve_contMDiffAt_interior Q hQ f hf0 hfSmooth hadd ht.1
  have hTo : IsOpen T := by
    apply isOpen_iff_mem_nhds.2
    intro t ht
    have h₁ : ∀ᶠ s : ℝ in 𝓝 t, |s| < 1 :=
      (continuous_abs.continuousAt : ContinuousAt (fun s : ℝ => |s|) t).preimage_mem_nhds (isOpen_Iio.mem_nhds ht.1)
    have h₂ := (hfAt t ht).continuousAt.preimage_mem_nhds (a.open_target.mem_nhds ht.2)
    filter_upwards [h₁,h₂] with s hs₁ hs₂
    exact ⟨hs₁,hs₂⟩
  have hg : ContDiffOn ℝ ∞ g T := by
    intro t ht
    exact (((hai.contMDiffAt (a.open_target.mem_nhds ht.2)).comp t (hfAt t ht)).contDiffAt).contDiffWithinAt
  obtain ⟨ℓ,hℓ⟩ := exists_continuous_dual_eq_one v hv0
  let A := vectorComplementEquiv v ℓ hℓ
  have hA : ∀ t : ℝ, A (t,0) = t • v := by
    intro t
    simp only [A,vectorComplementEquiv_apply,ZeroMemClass.coe_zero,add_zero]
  obtain ⟨e,he,he0,hezero,hes,heis⟩ := local_curve_smooth_product_map μ S hSo hS0 hμ0 hμ hl hr g T hTo hT0 hg0 hg hv A hA
  let b := e.trans a
  let σ : ℓ.ker → H := fun z => a (A (0,z))
  have hb0 : (0 : ℝ × ℓ.ker) ∈ b.source := by
    refine ⟨he0,?_⟩
    change e 0 ∈ a.source
    rw [hezero]
    exact ha0
  have hA0 : A (0,0) = 0 := A.map_zero
  have hbzero : b 0 = Q.one := by change a (e 0) = Q.one; rw [hezero,ha1]
  have hσ0 : σ 0 = Q.one := by change a (A (0,0)) = Q.one; rw [hA0,ha1]
  refine ⟨v,ℓ,hv0,hℓ,vectorComplement_dimension v ℓ hℓ,b,σ,hb0,hbzero,hσ0,?_,?_,?_⟩
  · intro p hp
    change p ∈ e.source ∧ e p ∈ a.source at hp
    have heS := (hes.contDiffAt (e.open_source.mem_nhds hp.1)).contMDiffAt
    exact ((ha.contMDiffAt (a.open_source.mem_nhds hp.2)).comp p heS).contMDiffWithinAt
  · intro x hx
    change x ∈ a.target ∧ a.symm x ∈ e.target at hx
    have haS := hai.contMDiffAt (a.open_target.mem_nhds hx.1)
    have heS := (heis.contDiffAt (e.open_target.mem_nhds hx.2)).contMDiffAt
    exact (heS.comp x haS).contMDiffWithinAt
  · have hgCont : ContinuousAt g 0 := hgSmooth.continuousAt
    have hfirst : ContinuousAt (fun p : ℝ × ℓ.ker => g p.1) 0 := by
      change Filter.Tendsto (fun p : ℝ × ℓ.ker => g p.1) (𝓝 0) (𝓝 (g 0))
      exact hgCont.tendsto.comp
        (continuousAt_fst : ContinuousAt (Prod.fst : ℝ × ℓ.ker → ℝ) (0 : ℝ × ℓ.ker)).tendsto
    have hsecond : ContinuousAt (fun p : ℝ × ℓ.ker => A (0,p.2)) 0 :=
      (A.continuous.comp ((continuous_const : Continuous (fun _ : ℝ × ℓ.ker => (0 : ℝ))).prodMk continuous_snd)).continuousAt
    have hpair : ContinuousAt (fun p : ℝ × ℓ.ker => (g p.1,A (0,p.2))) 0 := hfirst.prodMk hsecond
    have hpT : Filter.Tendsto (fun p : ℝ × ℓ.ker => (g p.1,A (0,p.2))) (𝓝 0) (𝓝 (0,0)) := by
      simpa only [Prod.fst_zero,Prod.snd_zero,hg0,hA0] using hpair.tendsto
    have hfT' : Filter.Tendsto (fun p : ℝ × ℓ.ker => f p.1) (𝓝 0) (𝓝 Q.one) :=
      hfT.comp continuousAt_fst.tendsto
    filter_upwards [hpT.eventually (hSo.mem_nhds hS0),hfT'.eventually (a.open_target.mem_nhds htarget)] with p hp hft
    have hh := hrel (g p.1,A (0,p.2)) hp
    change Q.mulRel (a (a.symm (f p.1))) (σ p.2) (a (μ (g p.1,A (0,p.2)))) at hh
    rw [a.right_inv hft] at hh
    change Q.mulRel (f p.1) (σ p.2) (a (e p))
    rw [he]
    exact hh
end DirectedCycles
