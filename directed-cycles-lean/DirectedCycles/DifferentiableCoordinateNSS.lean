import DirectedCycles.DifferentiableDoubling
import DirectedCycles.NormGrowthNSS
import DirectedCycles.LocalEscapeMaps
import DirectedCycles.LocalSubgroupTransport

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A differentiable local multiplication in genuine identity coordinates
produces an actual NSS identity neighbourhood, using doubling growth. -/
theorem cyclic_nss_neighbourhood_of_differentiable_coordinates
    (chart : G → E) (unchart : E → G) (V : Set G) (hV : V ∈ 𝓝 (1 : G))
    (hc : ContinuousAt chart 1) (hc1 : chart 1 = 0) (hu0 : unchart 0 = 1)
    (hleft : ∀ x ∈ V, unchart (chart x) = x)
    (hright : (fun x => chart (unchart x)) =ᶠ[𝓝 (0 : E)] id)
    (hmul : DifferentiableAt ℝ (fun p : E × E => chart (unchart p.1*unchart p.2)) (0,0)) :
    ∃ W : Set G, W ∈ 𝓝 (1 : G) ∧ ∀ x : G, (∀ n : ℕ, x^n ∈ W) → x = 1 := by
  let μ : E × E → E := fun p => chart (unchart p.1*unchart p.2)
  have hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id := by
    simpa only [μ,hu0,mul_one] using hright
  have hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id := by
    simpa only [μ,hu0,one_mul] using hright
  have hdiff := hasFDerivAt_diagonal_twice μ hmul hl hr
  obtain ⟨r,hr0,hexpand⟩ := exists_doubling_expansion (fun x => μ (x,x))
    (by simp only [μ,hu0,one_mul,hc1]) hdiff
  let W := V ∩ chart ⁻¹' Metric.ball 0 r
  have hW : W ∈ 𝓝 (1 : G) := by
    apply Filter.inter_mem hV
    apply hc.preimage_mem_nhds
    rw [hc1]
    exact Metric.ball_mem_nhds 0 hr0
  have hcyclic : ∀ x : G, (∀ n : ℕ, x^n ∈ W) → x = 1 :=
    cyclic_nss_of_doubling_growth W (fun x => ‖chart x‖) (3/2) r (by norm_num)
      (fun _ _ => norm_nonneg _) (by
        intro x hx he
        have hc0 : chart x = 0 := norm_eq_zero.mp he
        rw [← hleft x hx.1,hc0,hu0])
      (fun x hx => le_of_lt (by simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hx.2)) (by
        intro x hx _
        have hcx : ‖chart x‖ < r := by simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hx.2
        simpa only [μ,hleft x hx.1] using hexpand (chart x) hcx)
  exact ⟨W,hW,hcyclic⟩

/-- Differentiable coordinates exclude every nontrivial subgroup in an
actual identity neighbourhood. -/
theorem nss_neighbourhood_of_differentiable_coordinates
    (chart : G → E) (unchart : E → G) (V : Set G) (hV : V ∈ 𝓝 (1 : G))
    (hc : ContinuousAt chart 1) (hc1 : chart 1 = 0) (hu0 : unchart 0 = 1)
    (hleft : ∀ x ∈ V, unchart (chart x) = x)
    (hright : (fun x => chart (unchart x)) =ᶠ[𝓝 (0 : E)] id)
    (hmul : DifferentiableAt ℝ (fun p : E × E => chart (unchart p.1*unchart p.2)) (0,0)) :
    ∃ W : Set G, W ∈ 𝓝 (1 : G) ∧ (LocalGroupAlgebra.ofGroup G).IsNSS W := by
  obtain ⟨W,hW,hcyclic⟩ := cyclic_nss_neighbourhood_of_differentiable_coordinates
    chart unchart V hV hc hc1 hu0 hleft hright hmul
  refine ⟨W,hW,?_⟩
  intro H hH hHW x hx
  apply hcyclic x
  intro n
  have hp := hH.powerIn hx n
  have hxn : x^n ∈ H := (LocalGroupAlgebra.ofGroup_powerIn_iff H x n).1 hp
  exact hHW hxn
end DirectedCycles
