import DirectedCycles.LieOneParameterCoordinateDerivative
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false
open scoped Topology Manifold ContDiff
open IsManifold
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) 2 G]

include hLie in
/-- A continuous real one-parameter homomorphism into a C2 Banach Lie group is
manifold-differentiable at the identity. -/
theorem lieGroup_one_parameter_mdifferentiableAt_zero
    (φ : ℝ → G) (hφ0 : φ 0 = 1) (hφcont : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) :
    MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) φ 0 := by
  obtain ⟨v,hv,_⟩ := lieGroup_one_parameter_coordinate_derivative (E := E) φ hφ0 hφcont hφadd
  let e := chartAt E (1 : G)
  have h1 : (1 : G) ∈ e.source := mem_chart_source E 1
  have hc : e 1 ∈ e.target := e.mapsTo h1
  have he : e ∈ maximalAtlas 𝓘(ℝ,E) 1 G := chart_mem_maximalAtlas (1 : G)
  have hInv : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) 1 e.symm (e 1) :=
    contMDiffAt_symm_of_mem_maximalAtlas he hc
  have hcoord : DifferentiableAt ℝ (fun t => e (φ t)) 0 := by
    simpa only [e,sub_add_cancel] using hv.differentiableAt.add_const (e 1)
  have hh := (hInv.mdifferentiableAt one_ne_zero).comp_of_eq 0 hcoord.mdifferentiableAt
    (show e (φ 0) = e 1 by rw [hφ0])
  apply hh.congr_of_eventuallyEq
  have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), φ t ∈ e.source :=
    hφcont.preimage_mem_nhds (by simpa only [hφ0] using e.open_source.mem_nhds h1)
  filter_upwards [hnear] with t ht
  exact (e.left_inv ht).symm

include hLie in
/-- Translation propagates the constructed identity derivative to every real
parameter of a continuous one-parameter homomorphism. -/
theorem lieGroup_one_parameter_mdifferentiable
    (φ : ℝ → G) (hφ0 : φ 0 = 1) (hφcont : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) :
    MDifferentiable 𝓘(ℝ,ℝ) 𝓘(ℝ,E) φ := by
  have hzero := lieGroup_one_parameter_mdifferentiableAt_zero (E := E) φ hφ0 hφcont hφadd
  intro x
  have hshift : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun t : ℝ => t-x) x :=
    ((differentiableAt_id : DifferentiableAt ℝ (fun t : ℝ => t) x).sub_const x).mdifferentiableAt
  have hc := hzero.comp_of_eq x hshift (sub_self x)
  have hl : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (fun g : G => φ x*g) (φ (x-x)) :=
    mdifferentiableAt_mul_left
  apply (hl.comp x hc).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => by simpa only [Function.comp_apply,add_sub_cancel] using hφadd x (t-x))
end DirectedCycles
