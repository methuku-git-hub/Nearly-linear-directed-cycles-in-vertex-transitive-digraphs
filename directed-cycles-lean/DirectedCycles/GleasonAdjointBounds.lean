import DirectedCycles.GleasonAdjointRiemannSum

set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- All adjoint operators along short radial segments admit one uniform
bound, derived from continuity of the actual adjoint representation. -/
theorem exists_coordinateAdjoint_radial_bound : ∃ M σ : ℝ, 0 < M ∧ 0 < σ ∧
    ∀ y : E, ‖y‖ ≤ σ → ∀ t : ℝ, |t| ≤ 1 →
      ‖coordinateAdjoint D e (coordinateExp D e (t • y))‖ ≤ M := by
  let M : ℝ := ‖(1 : E →L[ℝ] E)‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hc := (coordinateAdjoint_contDiff D e).continuous.norm.continuousAt (x := (0 : E))
  have hnear : ∀ᶠ y : E in 𝓝 0, ‖coordinateAdjoint D e (coordinateExp D e y)‖ < M := by
    have hval : ‖coordinateAdjoint D e (coordinateExp D e (0 : E))‖ < M := by
      simp only [coordinateExp_zero,coordinateAdjoint_one]
      dsimp [M]
      linarith
    exact hc.eventually (gt_mem_nhds hval)
  obtain ⟨δ,hδ,hδB⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨M,δ/2,hM,by positivity,?_⟩
  intro y hy t ht
  have hmem : t • y ∈ Metric.ball (0 : E) δ := by
    rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs]
    have hh := mul_le_mul_of_nonneg_right ht (norm_nonneg y)
    nlinarith
  exact (hδB hmem).le

omit [FiniteDimensional ℝ E] in
/-- Total variation of the finite adjoint sum is uniformly bounded by
the norm of the input vector, independently of the subdivision. -/
theorem coordinateAdjoint_riemann_variation_bound {M σ : ℝ}
    (hbound : ∀ y : E, ‖y‖ ≤ σ → ∀ t : ℝ, |t| ≤ 1 →
      ‖coordinateAdjoint D e (coordinateExp D e (t • y))‖ ≤ M)
    (y z : E) (hy : ‖y‖ ≤ σ) (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range n, ‖(1/(n : ℝ)) •
      coordinateAdjoint D e (coordinateExp D e ((-((k : ℝ)/n)) • y)) z‖) ≤ M*‖z‖ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht (k : ℕ) (hk : k < n) : |(-((k : ℝ)/n))| ≤ 1 := by
    rw [abs_neg,abs_of_nonneg (by positivity)]
    exact (div_le_one hnR).mpr (by exact_mod_cast hk.le)
  have hb (k : ℕ) (hk : k ∈ Finset.range n) :
      ‖(1/(n : ℝ)) • coordinateAdjoint D e (coordinateExp D e ((-((k : ℝ)/n)) • y)) z‖ ≤
        (1/(n : ℝ))*(M*‖z‖) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 1/(n : ℝ))]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact ((coordinateAdjoint D e _).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (hbound y hy _ (ht k (Finset.mem_range.mp hk))) (norm_nonneg z))
  have h := Finset.sum_le_sum hb
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at h
  exact h.trans_eq (by field_simp)

end DirectedCycles.GleasonLieAlgebra
