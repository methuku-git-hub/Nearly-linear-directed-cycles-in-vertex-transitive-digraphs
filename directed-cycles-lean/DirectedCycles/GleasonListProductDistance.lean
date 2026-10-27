module

public import DirectedCycles.GleasonMetricBasics

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles.GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- A finite ordered-product comparison with one uniform factor of two.
Only the actual suffix products of the comparison family must stay small;
there is no exponential accumulation of Lipschitz constants. -/
theorem list_product_distance (L : List (G × G))
    (hstep : ∀ p ∈ L, D.metric.dist p.1 p.2 ≤ 1/D.constant)
    (hsuffix : ∀ U V : List (G × G), U++V=L →
      D.gauge ((V.map Prod.snd).prod) ≤ 1/D.constant) :
    D.metric.dist ((L.map Prod.fst).prod) ((L.map Prod.snd).prod) ≤
      2*(L.map (fun p => D.metric.dist p.1 p.2)).sum := by
  induction L with
  | nil => simp only [List.map_nil,List.prod_nil,List.sum_nil,mul_zero,D.metric.dist_self,le_refl]
  | cons p L ih =>
    have ht : ∀ q ∈ L, D.metric.dist q.1 q.2 ≤ 1/D.constant :=
      fun q hq => hstep q (by simp only [List.mem_cons]; exact Or.inr hq)
    have hs : ∀ U V : List (G × G), U++V=L → D.gauge ((V.map Prod.snd).prod) ≤ 1/D.constant := by
      intro U V hUV
      exact hsuffix (p::U) V (by simp only [List.cons_append,hUV])
    have htail := ih ht hs
    have hp := hstep p (by simp)
    have hlast := hsuffix [p] L rfl
    have hright := D.dist_mul_right_le_two p.1 p.2 ((L.map Prod.snd).prod) hp hlast
    have htri := D.metric.dist_triangle (p.1*(L.map Prod.fst).prod)
      (p.1*(L.map Prod.snd).prod) (p.2*(L.map Prod.snd).prod)
    rw [D.left_invariant] at htri
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    exact (htri.trans (add_le_add htail hright)).trans_eq (by ring)

end DirectedCycles.GleasonMetricData
