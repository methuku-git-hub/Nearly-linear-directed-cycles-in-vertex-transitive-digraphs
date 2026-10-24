import DirectedCycles.LocalGroupAlgebra
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Analysis.Normed.Module.Basic

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E]

/-- Actual local multiplication transported through an identity chart satisfies
both identity axes and local associativity. Every use of multiplication is
supported by a relation on a genuine neighbourhood of the identity pair. -/
theorem local_coordinate_multiplication_laws (L : LocalGroupAlgebra G)
    (a : OpenPartialHomeomorph E G) (hsource : (0 : E) ∈ a.source)
    (ha : a 0 = L.one) (μ : E × E → E) (hμ0 : μ (0,0) = 0)
    (hμ : ContinuousAt μ (0,0))
    (hrel : ∀ᶠ p : E × E in 𝓝 (0,0), L.mulRel (a p.1) (a p.2) (a (μ p))) :
    (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id ∧
    (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id ∧
    ∀ᶠ p : E × E in 𝓝 (0,0),
      (fun z => μ (μ (p.1,p.2),z)) =ᶠ[𝓝 (0 : E)] (fun z => μ (p.1,μ (p.2,z))) := by
  have hS : a.source ∈ 𝓝 (0 : E) := a.open_source.mem_nhds hsource
  have hμT : Filter.Tendsto μ (𝓝 (0,0)) (𝓝 (0 : E)) := by
    simpa only [hμ0] using hμ.tendsto
  have hlT : Filter.Tendsto (fun x : E => (x,(0 : E))) (𝓝 0) (𝓝 (0,0)) :=
    continuousAt_id.prodMk continuousAt_const
  have hrT : Filter.Tendsto (fun x : E => ((0 : E),x)) (𝓝 0) (𝓝 (0,0)) :=
    continuousAt_const.prodMk continuousAt_id
  refine ⟨?_,?_,?_⟩
  · filter_upwards [hlT.eventually hrel,(hμT.comp hlT).eventually hS,hS] with x hx hm hs
    apply a.injOn hm hs
    exact L.unique (by simpa only [ha,Function.comp_def] using hx) (L.mul_one _)
  · filter_upwards [hrT.eventually hrel,(hμT.comp hrT).eventually hS,hS] with x hx hm hs
    apply a.injOn hm hs
    exact L.unique (by simpa only [ha,Function.comp_def] using hx) (L.one_mul _)
  · have hx : Filter.Tendsto (fun q : (E × E) × E => q.1.1) (𝓝 ((0,0),0)) (𝓝 0) :=
      continuousAt_fst.fst
    have hy : Filter.Tendsto (fun q : (E × E) × E => q.1.2) (𝓝 ((0,0),0)) (𝓝 0) :=
      continuousAt_fst.snd
    have hz : Filter.Tendsto (fun q : (E × E) × E => q.2) (𝓝 ((0,0),0)) (𝓝 0) :=
      continuousAt_snd
    have hab := hμT.comp (hx.prodMk_nhds hy)
    have hbc := hμT.comp (hy.prodMk_nhds hz)
    have hl := hμT.comp (hab.prodMk_nhds hz)
    have hr := hμT.comp (hx.prodMk_nhds hbc)
    have hall : ∀ᶠ q : (E × E) × E in 𝓝 ((0,0),0),
        μ (μ (q.1.1,q.1.2),q.2) = μ (q.1.1,μ (q.1.2,q.2)) := by
      filter_upwards [(hx.prodMk_nhds hy).eventually hrel,(hy.prodMk_nhds hz).eventually hrel,
        (hab.prodMk_nhds hz).eventually hrel,(hx.prodMk_nhds hbc).eventually hrel,
        hl.eventually hS,hr.eventually hS] with q hab hbc hl hr hls hrs
      apply a.injOn hls hrs
      exact L.assoc hab hbc hl hr
    rw [nhds_prod_eq] at hall
    exact hall.curry
end DirectedCycles
