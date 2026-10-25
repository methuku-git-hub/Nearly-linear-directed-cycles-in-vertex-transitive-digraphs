module

public import DirectedCycles.LocalExponentialProductBounds
public import DirectedCycles.LocalExponentialRadialLaw
public import DirectedCycles.LocalConjugates

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
namespace LocalExponentialData
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] {L : LocalGroupAlgebra G} (D : LocalExponentialData (E := E) L)

/-- Actual local conjugate words have their middle coordinate plus a
controlled error. For each finite trapping length the error can be made
small enough uniformly in the conjugating vector. -/
theorem conjugate_word_error {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ x y : E, ‖x‖ < r → ‖y‖ < r → ∀ z : G,
      L.Product [L.inv (D.chart x),D.chart y,D.chart x] z →
      ∃ w : E, ‖w‖ ≤ ‖y‖+ε*(4*‖x‖+3*‖y‖) ∧ D.chart w = z := by
  obtain ⟨a,ha,hadd⟩ := D.product_add_error hε
  refine ⟨min (a/8) (D.radius/4),lt_min (by positivity) (by have := D.radius_pos; positivity),?_⟩
  intro x y hx hy z hp
  have hxa : ‖x‖ < a/8 := hx.trans_le (min_le_left _ _)
  have hya : ‖y‖ < a/8 := hy.trans_le (min_le_left _ _)
  have hxr : 2*‖x‖ < D.radius := by have := hx.trans_le (min_le_right _ _); have := D.radius_pos; linarith
  obtain ⟨u,hu,huRel⟩ := hadd (-x) y (by rw [norm_neg]; linarith) (by linarith)
  rw [norm_neg] at hu
  have huBound : ‖u‖ ≤ 2*(‖x‖+‖y‖) := by
    have htri : ‖-x+y‖ ≤ ‖x‖+‖y‖ := by simpa only [norm_neg] using norm_add_le (-x) y
    have hnorm := norm_le_insert' u (-x+y)
    have he := mul_le_mul_of_nonneg_right hε1 (add_nonneg (norm_nonneg x) (norm_nonneg y))
    nlinarith
  obtain ⟨w,hw,hwRel⟩ := hadd u x (by linarith) (by linarith)
  have herror : ‖w-y‖ ≤ ε*(4*‖x‖+3*‖y‖) := by
    calc
      ‖w-y‖ = ‖(w-(u+x))+(u-(-x+y))‖ := by congr 1; abel
      _ ≤ ‖w-(u+x)‖+‖u-(-x+y)‖ := norm_add_le _ _
      _ ≤ ε*(‖u‖+‖x‖)+ε*(‖x‖+‖y‖) := add_le_add hw hu
      _ ≤ ε*(4*‖x‖+3*‖y‖) := by nlinarith
  refine ⟨w,?_,?_⟩
  · have ht := norm_le_insert' w y
    linarith
  · obtain ⟨u',x',hu',hx',hm⟩ := hp.split L
      (a := [L.inv (D.chart x),D.chart y]) (b := [D.chart x]) rfl (by simp) (by simp)
    have hxEq : x' = D.chart x := (LocalGroupAlgebra.Product.singleton_iff L).1 hx'
    have huRel' : L.mulRel (L.inv (D.chart x)) (D.chart y) u' :=
      (LocalGroupAlgebra.Product.pair_iff L _ _ _).1 hu'
    rw [D.inv_chart hxr] at huRel
    have huEq : D.chart u = u' := L.unique huRel huRel'
    exact L.unique (by simpa only [huEq] using hwRel) (by simpa only [hxEq] using hm)
end LocalExponentialData
end DirectedCycles
