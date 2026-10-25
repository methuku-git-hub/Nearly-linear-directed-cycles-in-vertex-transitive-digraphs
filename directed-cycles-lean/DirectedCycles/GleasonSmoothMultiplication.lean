module

public import DirectedCycles.GleasonMultiplicationDerivative

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology ContDiff
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- The proved derivative formula inherits every finite order of
regularity already known for multiplication itself. -/
theorem coordinateMulDerivative_contDiffOn {s : Set (E × E)} (n : ℕ)
    (hμ : ContDiffOn ℝ n (coordinateMul D e) s)
    (hu : ∀ p ∈ s, IsUnit (coordinateAdjointAverage D e (coordinateMul D e p))) :
    ContDiffOn ℝ n (coordinateMulDerivative D e) s := by
  have hI : ContDiffOn ℝ n (fun p => Ring.inverse (coordinateAdjointAverage D e (coordinateMul D e p))) s := by
    intro p hp
    exact ((coordinateAdjointAverage_inverse_contDiffAt D e _ (hu p hp)).of_le (by simp)).comp_contDiffWithinAt p (hμ p hp)
  have hA : ContDiff ℝ n (coordinateAdjointAverage D e) := (coordinateAdjointAverage_contDiff D e).of_le (by simp)
  have hX : ContDiff ℝ n (fun p : E × E => coordinateAdjointAverage D e p.1) := hA.comp contDiff_fst
  have hY : ContDiff ℝ n (fun p : E × E => coordinateAdjointAverage D e p.2) := hA.comp contDiff_snd
  have hQ : ContDiff ℝ n (fun p : E × E => coordinateAdjoint D e ((coordinateExp D e p.2)⁻¹)) := by
    have hn : ContDiff ℝ n (fun p : E × E => -p.2) := contDiff_snd.neg
    have h := ((coordinateAdjoint_contDiff D e).of_le (by simp : (n : WithTop ℕ∞) ≤ ∞)).comp hn
    simpa only [Function.comp_def,coordinateExp_neg] using h
  exact hI.clm_comp (((hQ.contDiffOn.clm_comp hX.contDiffOn).clm_comp contDiffOn_const).add
    (hY.contDiffOn.clm_comp contDiffOn_const))

/-- Actual multiplication in the constructed exponential coordinates is
smooth on a neighbourhood of the identity pair. The proof bootstraps the
derived joint derivative, starting from differentiability proved from
finite products, metric estimates and the actual group identities. -/
theorem coordinateMul_contDiff_near_zero : ∃ δ : ℝ, 0 < δ ∧
    ContDiffOn ℝ ∞ (coordinateMul D e) (Metric.ball (0 : E × E) δ) := by
  obtain ⟨δ,hδ,hdata⟩ := exists_coordinateMul_derivative_radius D e
  have hd (p : E × E) (hp : p ∈ Metric.ball (0 : E × E) δ) :=
    hdata p (by simpa only [Metric.mem_ball,dist_zero_right] using hp)
  have hdiff : DifferentiableOn ℝ (coordinateMul D e) (Metric.ball (0 : E × E) δ) :=
    fun p hp => (hd p hp).2.differentiableAt.differentiableWithinAt
  have hfinite (n : ℕ) : ContDiffOn ℝ n (coordinateMul D e) (Metric.ball (0 : E × E) δ) := by
    induction n with
    | zero => exact contDiffOn_zero.mpr hdiff.continuousOn
    | succ n ih =>
      rw [Nat.cast_add,Nat.cast_one]
      apply (contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball).mpr
      refine ⟨hdiff,by simp,?_⟩
      exact (coordinateMulDerivative_contDiffOn D e n ih (fun p hp => (hd p hp).1)).congr
        (fun p hp => (hd p hp).2.fderiv)
  exact ⟨δ,hδ,contDiffOn_infty.mpr hfinite⟩

/-- In particular, the actual local multiplication is smooth at the
identity pair, with no smooth group structure in the hypotheses. -/
theorem coordinateMul_contDiffAt_zero : ContDiffAt ℝ ∞ (coordinateMul D e) (0,0) := by
  obtain ⟨δ,hδ,h⟩ := coordinateMul_contDiff_near_zero D e
  exact h.contDiffAt (Metric.ball_mem_nhds _ hδ)

end DirectedCycles.GleasonLieAlgebra
