import DirectedCycles.LocalGroupSmoothness
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E H]

/-- Around each point of a smooth local group, all actual relative
differences of sufficiently nearby points lie in a prescribed identity
neighbourhood. The difference relation is defined on the whole cell pair. -/
theorem smooth_local_difference_cell (M : LocalGroupAlgebra H)
    (hM : LocalGroupSmoothness (E := E) M) (c : H) (V : Set H) (hV : V ∈ 𝓝 M.one) :
    ∃ O : Set H, IsOpen O ∧ c ∈ O ∧ ∀ x ∈ O, ∀ y ∈ O,
      ∃ z ∈ V, M.mulRel (M.inv x) y z := by
  obtain ⟨m,hm,hmrel⟩ := hM.smooth_mul (M.inv c) c ⟨M.one,M.inv_mul c⟩
  have hm1 : m (M.inv c,c) = M.one := M.unique hmrel.self_of_nhds (M.inv_mul c)
  have hpair : ContinuousAt (fun p : H × H => (M.inv p.1,p.2)) (c,c) :=
    (hM.continuous_inv.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
  have hθ : Filter.Tendsto (fun p : H × H => m (M.inv p.1,p.2)) (𝓝 (c,c)) (𝓝 M.one) := by
    simpa only [hm1,Function.comp_def] using (hm.continuousAt.comp (f := fun p : H × H => (M.inv p.1,p.2)) hpair).tendsto
  have hnear : ∀ᶠ p : H × H in 𝓝 (c,c), ∃ z ∈ V, M.mulRel (M.inv p.1) p.2 z := by
    filter_upwards [hpair.tendsto.eventually hmrel,hθ.eventually hV] with p hp hv
    exact ⟨m (M.inv p.1,p.2),hv,hp⟩
  obtain ⟨A,hA,B,hB,hAB⟩ := mem_nhds_prod_iff.mp hnear
  let O := interior A ∩ interior B
  refine ⟨O,isOpen_interior.inter isOpen_interior,
    ⟨mem_interior_iff_mem_nhds.mpr hA,mem_interior_iff_mem_nhds.mpr hB⟩,?_⟩
  intro x hx y hy
  exact hAB (show (x,y) ∈ A ×ˢ B from ⟨interior_subset hx.1,interior_subset hy.2⟩)
end DirectedCycles
