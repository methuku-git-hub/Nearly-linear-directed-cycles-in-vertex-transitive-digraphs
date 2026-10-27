module

public import DirectedCycles.LocalFinitePowerTrapping
public import DirectedCycles.DifferentiableDoubling

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiable identity coordinates and a genuine local product construct
an NSS neighbourhood in an actual local group. -/
theorem local_nss_neighbourhood_of_differentiable_coordinates (L : LocalGroupAlgebra G)
    (chart : G → E) (unchart : E → G) (V : Set G) (hV : V ∈ 𝓝 L.one)
    (hc : ContinuousAt chart L.one) (hu : ContinuousAt unchart 0)
    (hc1 : chart L.one = 0) (hu0 : unchart 0 = L.one)
    (hleft : ∀ x ∈ V, unchart (chart x) = x)
    (hright : (fun x => chart (unchart x)) =ᶠ[𝓝 (0 : E)] id)
    (m : G × G → G) (hm : ∀ᶠ p in 𝓝 (L.one,L.one), L.mulRel p.1 p.2 (m p))
    (hmul : DifferentiableAt ℝ (fun p : E × E => chart (m (unchart p.1,unchart p.2))) (0,0)) :
    ∃ W : Set G, W ∈ 𝓝 L.one ∧ L.IsNSS W ∧
      (∀ x : G, ∀ p : L.PowerSequence x, (∀ n, p.power n ∈ W) → x = L.one) ∧
      (∀ U : Set G, U ∈ 𝓝 L.one → ∃ M : ℕ, 1 ≤ M ∧
        ∀ x : G, (∀ n ≤ M, L.PowerIn W x n) → x ∈ U) := by
  let μ : E × E → E := fun p => chart (m (unchart p.1,unchart p.2))
  have hu' : Filter.Tendsto unchart (𝓝 0) (𝓝 L.one) := by simpa only [hu0] using hu.tendsto
  have hml : ∀ᶠ x in 𝓝 (0 : E), L.mulRel (unchart x) L.one (m (unchart x,L.one)) :=
    (hu'.prodMk_nhds tendsto_const_nhds).eventually hm
  have hmr : ∀ᶠ x in 𝓝 (0 : E), L.mulRel L.one (unchart x) (m (L.one,unchart x)) :=
    (Filter.Tendsto.prodMk_nhds tendsto_const_nhds hu').eventually hm
  have hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id := by
    filter_upwards [hml,hright] with x hx he
    dsimp only [μ]
    rw [hu0,L.unique hx (L.mul_one _)]
    exact he
  have hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id := by
    filter_upwards [hmr,hright] with x hx he
    dsimp only [μ]
    rw [hu0,L.unique hx (L.one_mul _)]
    exact he
  have hdiff := hasFDerivAt_diagonal_twice μ hmul hl hr
  have hmSelf : L.mulRel L.one L.one (m (L.one,L.one)) := hm.self_of_nhds
  have hm1 : m (L.one,L.one) = L.one := L.unique hmSelf (L.one_mul _)
  obtain ⟨r,hr0,hexpand⟩ := exists_doubling_expansion (fun x => μ (x,x))
    (by simp only [μ,hu0,hm1,hc1]) hdiff
  have hdiag : ∀ᶠ x in 𝓝 L.one, L.mulRel x x (m (x,x)) :=
    (continuousAt_id.prodMk continuousAt_id).eventually hm
  let W := V ∩ chart ⁻¹' Metric.ball 0 r ∩ {x | L.mulRel x x (m (x,x))}
  have hW : W ∈ 𝓝 L.one := by
    apply Filter.inter_mem _ hdiag
    apply Filter.inter_mem hV
    apply hc.preimage_mem_nhds
    rw [hc1]
    exact Metric.ball_mem_nhds 0 hr0
  have hzero : ∀ x ∈ W, ‖chart x‖ = 0 → x = L.one := by
    intro x hx he
    have hc0 : chart x = 0 := norm_eq_zero.mp he
    rw [← hleft x hx.1.1,hc0,hu0]
  have hbound : ∀ x ∈ W, ‖chart x‖ ≤ r := fun x hx => le_of_lt (by
    simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hx.1.2)
  have hgrowth : ∀ x ∈ W, ∀ y ∈ W, L.mulRel x x y → (3/2 : ℝ)*‖chart x‖ ≤ ‖chart y‖ := by
    intro x hx y _ hxy
    have hcx : ‖chart x‖ < r := by
      simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hx.1.2
    have hex := hexpand (chart x) hcx
    simpa only [μ,hleft x hx.1.1,L.unique hx.2 hxy] using hex
  refine ⟨W,hW,L.nss_of_doubling_growth W (fun x => ‖chart x‖) (3/2) r (by norm_num)
    (fun _ _ => norm_nonneg _) hzero hbound hgrowth,
    L.powerSequence_trivial_of_doubling_growth W (fun x => ‖chart x‖) (3/2) r (by norm_num)
    (fun _ _ => norm_nonneg _) hzero hbound hgrowth,?_⟩
  intro U hU
  have huU : unchart ⁻¹' U ∈ 𝓝 (0 : E) := hu'.eventually hU
  obtain ⟨ε,hε,hsmall⟩ := Metric.mem_nhds_iff.mp huU
  obtain ⟨M,hM,htrap⟩ := L.finite_power_trapping_of_doubling_growth W (fun x => ‖chart x‖)
    (3/2) r (by norm_num) hbound hgrowth hε
  refine ⟨M,hM,?_⟩
  intro x hx
  have hxW : x ∈ W := (L.powerIn_one W x).1 (hx 1 hM)
  have hcx : chart x ∈ Metric.ball 0 ε := by
    simpa only [Metric.mem_ball,dist_zero_right] using htrap x hx
  have hh := hsmall hcx
  change unchart (chart x) ∈ U at hh
  rwa [hleft x hxW.1.1] at hh
end DirectedCycles
