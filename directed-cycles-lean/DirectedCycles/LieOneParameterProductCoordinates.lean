module

public import DirectedCycles.LieOneParameterSmooth
public import DirectedCycles.LieOneParameterNonzero
public import DirectedCycles.VectorComplementDimension
public import DirectedCycles.LocalCurveProductCoordinates

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
open IsManifold
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E G] [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- A nontrivial continuous one-parameter homomorphism in a finite-dimensional
Lie group has actual local product coordinates along the curve and a transverse
space whose dimension is one less. -/
theorem lieGroup_one_parameter_product_coordinates
    (φ : ℝ → G) (hφ0 : φ 0 = 1) (hφcont : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (hnt : ∃ t : ℝ, φ t ≠ 1) :
    ∃ (v : E) (ℓ : E →L[ℝ] ℝ), v ≠ 0 ∧ ℓ v = 1 ∧
      Module.finrank ℝ ℓ.ker + 1 = Module.finrank ℝ E ∧
      ∃ a : OpenPartialHomeomorph (ℝ × ℓ.ker) G,
        (0 : ℝ × ℓ.ker) ∈ a.source ∧ a 0 = 1 ∧
        ∀ᶠ p : ℝ × ℓ.ker in 𝓝 (0 : ℝ × ℓ.ker),
          a p = φ p.1 * (chartAt E (1 : G)).symm ((p.2 : E)+(chartAt E (1 : G)) 1) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ,E)) (n := ∞)
  let e := chartAt E (1 : G)
  let c : E := e 1
  let chart : G → E := fun x => e x-c
  let unchart : E → G := fun y => e.symm (y+c)
  have h1 : (1 : G) ∈ e.source := mem_chart_source E 1
  have hc : c ∈ e.target := e.mapsTo h1
  have hchart : ContinuousAt chart 1 := (e.continuousAt h1).sub continuousAt_const
  have hc1 : chart 1 = 0 := sub_self _
  have hu0 : unchart 0 = 1 := by
    dsimp only [unchart]
    rw [zero_add]
    exact e.left_inv h1
  have hleft : ∀ x ∈ e.source, unchart (chart x) = x := by
    intro x hx
    dsimp only [unchart,chart]
    rw [sub_add_cancel]
    exact e.left_inv hx
  have hright : (fun x => chart (unchart x)) =ᶠ[𝓝 (0 : E)] id := by
    have hcont : ContinuousAt (fun x : E => x+c) 0 := continuousAt_id.add continuousAt_const
    have htarget : ∀ᶠ x in 𝓝 (0 : E), x+c ∈ e.target :=
      hcont.preimage_mem_nhds (by simpa only [zero_add] using e.open_target.mem_nhds hc)
    filter_upwards [htarget] with x hx
    dsimp only [chart,unchart,id]
    rw [e.right_inv hx,add_sub_cancel_right]
  have he : e ∈ maximalAtlas 𝓘(ℝ,E) ∞ G := chart_mem_maximalAtlas (1 : G)
  have heSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e (1 : G) :=
    contMDiffAt_of_mem_maximalAtlas he h1
  have heInvSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm c :=
    contMDiffAt_symm_of_mem_maximalAtlas he hc
  have hchartSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ chart (1 : G) :=
    heSmooth.sub contMDiffAt_const
  have hunchartSmooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ unchart (0 : E) := by
    have heInvSmooth' : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm ((0 : E)+c) := by
      simpa only [zero_add] using heInvSmooth
    exact heInvSmooth'.comp 0 (contMDiffAt_id.add contMDiffAt_const)
  have hmulSmooth : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞
      (fun p : E × E => unchart p.1*unchart p.2) (0,0) :=
    (hunchartSmooth.comp (0,0) contDiffAt_fst.contMDiffAt).mul (hunchartSmooth.comp (0,0) contDiffAt_snd.contMDiffAt)
  have hm : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞
      (fun p : E × E => chart (unchart p.1*unchart p.2)) (0,0) := by
    have hs : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ chart (unchart 0*unchart 0) := by
      simpa only [hu0,one_mul] using hchartSmooth
    exact hs.comp (0,0) hmulSmooth
  let μ : E × E → E := fun p => chart (unchart p.1*unchart p.2)
  have hμ : ContDiffAt ℝ ∞ μ (0,0) := hm.contDiffAt
  have hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id := by
    simpa only [μ,hu0,mul_one] using hright
  have hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id := by
    simpa only [μ,hu0,one_mul] using hright
  let f : ℝ → E := fun t => chart (φ t)
  have hf0 : f 0 = 0 := by dsimp only [f]; rw [hφ0,hc1]
  have hf : ContDiffAt ℝ ∞ f 0 := lieGroup_one_parameter_coordinate_smooth (E := E) φ hφ0 hφcont hφadd
  obtain ⟨v,hv0,hv⟩ := lieGroup_one_parameter_nonzero_derivative (E := E) φ hφ0 hφcont hφadd hnt
  obtain ⟨ℓ,hℓ⟩ := exists_continuous_dual_eq_one v hv0
  let A := vectorComplementEquiv v ℓ hℓ
  have hA : ∀ t : ℝ, A (t,0) = t • v := by
    intro t
    simp only [A,vectorComplementEquiv_apply,ZeroMemClass.coe_zero,add_zero]
  obtain ⟨b,hb,hb0,hbzero,_,_⟩ := local_curve_product_coordinates μ hμ hl hr f hf0 hf hv A hA
  let a := (b.trans (Homeomorph.addRight c).toOpenPartialHomeomorph).trans e.symm
  have ha0 : (0 : ℝ × ℓ.ker) ∈ a.source := by
    change (0 : ℝ × ℓ.ker) ∈ (b.trans (Homeomorph.addRight c).toOpenPartialHomeomorph).source ∩
      (b.trans (Homeomorph.addRight c).toOpenPartialHomeomorph) ⁻¹' e.target
    constructor
    · exact ⟨hb0,Set.mem_univ _⟩
    · change b 0+c ∈ e.target
      rw [hbzero,zero_add]
      exact hc
  have ha1 : a 0 = 1 := by
    change e.symm (b 0+c) = 1
    rw [hbzero,zero_add]
    exact e.left_inv h1
  refine ⟨v,ℓ,hv0,hℓ,vectorComplement_dimension v ℓ hℓ,a,ha0,ha1,?_⟩
  have hp : ContinuousAt (fun p : ℝ × ℓ.ker => φ p.1) 0 := by
    have hh : ContinuousAt φ ((0 : ℝ × ℓ.ker).1) := hφcont
    exact hh.comp continuousAt_fst
  have hy : ContinuousAt (fun p : ℝ × ℓ.ker => unchart (p.2 : E)) 0 := by
    have hh : ContinuousAt unchart (((0 : ℝ × ℓ.ker).2 : ℓ.ker) : E) := hunchartSmooth.continuousAt
    have hys : ContinuousAt (fun p : ℝ × ℓ.ker => (p.2 : E)) 0 :=
      (continuous_subtype_val.comp continuous_snd).continuousAt
    exact hh.comp (f := fun p : ℝ × ℓ.ker => (p.2 : E)) hys
  have hprod : ContinuousAt (fun p : ℝ × ℓ.ker => φ p.1*unchart (p.2 : E)) 0 := hp.mul hy
  have hφnear : ∀ᶠ p : ℝ × ℓ.ker in 𝓝 (0 : ℝ × ℓ.ker), φ p.1 ∈ e.source :=
    hp.preimage_mem_nhds (by simpa only [Prod.fst_zero,hφ0] using e.open_source.mem_nhds h1)
  have hprodnear : ∀ᶠ p : ℝ × ℓ.ker in 𝓝 (0 : ℝ × ℓ.ker), φ p.1*unchart (p.2 : E) ∈ e.source :=
    hprod.preimage_mem_nhds (by simpa only [Prod.fst_zero,Prod.snd_zero,ZeroMemClass.coe_zero,hφ0,hu0,one_mul] using e.open_source.mem_nhds h1)
  filter_upwards [hφnear,hprodnear] with p hp' hprod'
  change e.symm (b p+c) = φ p.1*unchart (p.2 : E)
  rw [hb]
  have hA2 : A (0,p.2) = (p.2 : E) := by simp only [A,vectorComplementEquiv_apply,zero_smul,zero_add]
  change unchart (chart (unchart (chart (φ p.1))*unchart (A (0,p.2)))) = φ p.1*unchart (p.2 : E)
  rw [hleft (φ p.1) hp',hA2,hleft _ hprod']
end DirectedCycles
