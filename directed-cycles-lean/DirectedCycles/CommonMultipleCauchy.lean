module

public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Topology
namespace DirectedCycles
variable {X : Type*} [PseudoMetricSpace X]

/-- A bound that decays with the initial subdivision and is uniform under
all further integer refinements makes the entire sequence Cauchy. -/
theorem cauchySeq_of_common_multiple (a : ℕ → X) (K : ℝ)
    (h : ∀ n m : ℕ, 0 < n → 0 < m → dist (a n) (a (n*m)) ≤ K/(n : ℝ)) :
    CauchySeq a := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hev : ∀ᶠ n : ℕ in atTop, K/(n : ℝ) < ε/2 :=
    (tendsto_const_div_atTop_nhds_zero_nat K).eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨max N 1,?_⟩
  intro n hn m hm
  have hn0 : 0 < n := by omega
  have hm0 : 0 < m := by omega
  have hnm := h n m hn0 hm0
  have hmn := h m n hm0 hn0
  rw [Nat.mul_comm m n,dist_comm (a m)] at hmn
  have ht := dist_triangle (a n) (a (n*m)) (a m)
  have hnK := hN n (by omega)
  have hmK := hN m (by omega)
  linarith

/-- The same refinement bound survives in the actual limit; no rate of
convergence is assumed separately. -/
theorem dist_limit_le_of_common_multiple {a : ℕ → X} {x : X} {K : ℝ}
    (ha : Tendsto a atTop (𝓝 x))
    (h : ∀ n m : ℕ, 0 < n → 0 < m → dist (a n) (a (n*m)) ≤ K/(n : ℝ))
    (n : ℕ) (hn : 0 < n) : dist (a n) x ≤ K/(n : ℝ) := by
  have hmul : Tendsto (fun m : ℕ => n*m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hn) tendsto_id
  have ht : Tendsto (fun m : ℕ => dist (a n) (a (n*m))) atTop (𝓝 (dist (a n) x)) :=
    tendsto_const_nhds.dist (ha.comp hmul)
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact h n m hn (by omega)
end DirectedCycles
