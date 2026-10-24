import DirectedCycles.GleasonExponentialBiLipschitz
import DirectedCycles.GleasonLocalCoordinateLaw

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- Multiplication in the actual exponential coordinates has a quadratic
bilinear-size error. This is a quantitative estimate, not an assumption of
continuous differentiability. -/
theorem coordinateMul_quadratic_error : ∃ K ρ : ℝ, 0 < K ∧ 0 < ρ ∧
    ∀ x y : E, ‖x‖ < ρ → ‖y‖ < ρ →
      ‖coordinateMul D e (x,y)-x-y‖ ≤ K*‖x‖*‖y‖ := by
  obtain ⟨a,b,s,ha,_hb,hs,hbi⟩ := exists_coordinateExp_bilipschitz D e
  obtain ⟨A,hA,hspeed⟩ := exists_coordinate_speed D e
  obtain ⟨r,hrpos,hr,hp⟩ := D.exists_trotter_radius
  have hC := D.constant_pos
  have hμ : ∀ᶠ p : E × E in 𝓝 (0,0), ‖coordinateMul D e p‖ < s := by
    have h := (coordinateMul_continuousAt_zero D e).norm.preimage_mem_nhds
      (gt_mem_nhds (by simpa only [coordinateMul_zero,norm_zero] using hs))
    exact h
  have hsum : ∀ᶠ p : E × E in 𝓝 (0,0), ‖p.1+p.2‖ < s := by
    have hc : ContinuousAt (fun p : E × E => ‖p.1+p.2‖) (0,0) :=
      (continuous_fst.add continuous_snd).norm.continuousAt
    exact hc.preimage_mem_nhds (gt_mem_nhds (by simpa only [zero_add,norm_zero] using hs))
  have hcprod : Continuous (fun p : E × E => coordinateExp D e p.1*coordinateExp D e p.2) :=
    ((continuous_coordinateExp D e).comp continuous_fst).mul ((continuous_coordinateExp D e).comp continuous_snd)
  have hprod : ∀ᶠ p : E × E in 𝓝 (0,0),
      coordinateExp D e p.1*coordinateExp D e p.2 ∈ (coordinateChart D e).target := by
    apply hcprod.continuousAt.preimage_mem_nhds
    simpa only [coordinateExp_zero,one_mul] using
      (coordinateChart D e).open_target.mem_nhds (one_mem_coordinateChart_target D e)
  have hnear : ∀ᶠ p : E × E in 𝓝 (0,0), ‖coordinateMul D e p‖ < s ∧ ‖p.1+p.2‖ < s ∧
      coordinateExp D e p.1*coordinateExp D e p.2 ∈ (coordinateChart D e).target := by
    filter_upwards [hμ,hsum,hprod] with p hp₁ hp₂ hp₃
    exact ⟨hp₁,hp₂,hp₃⟩
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp hnear
  let ρ := min (δ/2) (r/(4*A))
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  refine ⟨4*D.constant*A^2/a,ρ,by positivity,hρ,?_⟩
  intro x y hx hy
  have hpxy : (x,y) ∈ Metric.ball (0 : E × E) δ := by
    rw [Metric.mem_ball,dist_zero_right,Prod.norm_def]
    have hρδ : ρ < δ := (min_le_left _ _).trans_lt (by linarith)
    exact max_lt (hx.trans hρδ) (hy.trans hρδ)
  obtain ⟨hm,hsumxy,hprodxy⟩ := hδb hpxy
  have hsmall : A*(‖x‖+‖y‖) ≤ r := by
    have hρr := (le_div_iff₀ (show 0 < 4*A by positivity)).mp (min_le_right (δ/2) (r/(4*A)))
    nlinarith
  have he := coordinateExp_add_error D e hp hr hA.le hspeed x y hsmall
  have hl := (hbi (coordinateMul D e (x,y)) (x+y) hm.le hsumxy.le).1
  rw [coordinateExp_mul D e hprodxy] at hl
  have hb := hl.trans he
  have heq : ‖(x+y)-coordinateMul D e (x,y)‖ = ‖coordinateMul D e (x,y)-x-y‖ := by
    rw [norm_sub_rev]
    congr 1
    abel
  rw [heq] at hb
  have hdivide := (le_div_iff₀ ha).mpr (show ‖coordinateMul D e (x,y)-x-y‖*a ≤ 4*D.constant*A^2*‖x‖*‖y‖ by nlinarith)
  exact hdivide.trans_eq (by ring)

end DirectedCycles.GleasonLieAlgebra
