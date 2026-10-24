import DirectedCycles.GleasonCoordinateHomError
import DirectedCycles.NormedAlgebraCurveGenerator
import Mathlib.Analysis.Asymptotics.Lemmas

set_option autoImplicit false
open Filter Topology Asymptotics
open scoped Topology ContDiff
namespace DirectedCycles.GleasonLieAlgebra
variable {G E A : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : GleasonLieAlgebra D ≃L[ℝ] E)
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The actual generator of an algebra-valued homomorphism along each
constructed coordinate curve. -/
noncomputable def homGenerator (F : ContinuousMonoidHom G A) (x : E) : A :=
  deriv (fun t : ℝ => F (coordinateExp D e (t • x))) 0

theorem homGenerator_hasDerivAt (F : ContinuousMonoidHom G A) (x : E) :
    HasDerivAt (fun t : ℝ => F (coordinateExp D e (t • x))) (homGenerator D e F x) 0 := by
  apply DifferentiableAt.hasDerivAt
  apply (normedAlgebra_one_parameter_contDiffAt_zero _ ?_ ?_ ?_).differentiableAt (by simp)
  · simp only [zero_smul,coordinateExp_zero,map_one]
  · exact (F.continuous.comp ((continuous_coordinateExp D e).comp (continuous_id.smul continuous_const))).continuousAt
  · intro s t
    simp only [coordinateExp_smul,OneParameter.eval_add,map_mul]

theorem homGenerator_exp (F : ContinuousMonoidHom G A) (x : E) (t : ℝ) :
    F (coordinateExp D e (t • x)) = NormedSpace.exp (t • homGenerator D e F x) := by
  apply normedAlgebra_curve_eq_exp _ ?_ ?_ (homGenerator_hasDerivAt D e F x) t
  · simp only [zero_smul,coordinateExp_zero,map_one]
  · intro s u
    simp only [coordinateExp_smul,OneParameter.eval_add,map_mul]

theorem homGenerator_smul (F : ContinuousMonoidHom G A) (c : ℝ) (x : E) :
    homGenerator D e F (c • x) = c • homGenerator D e F x := by
  have ht : HasDerivAt (fun t : ℝ => c*t) c 0 := by
    simpa only [mul_one,id_eq] using (hasDerivAt_id (0 : ℝ)).const_mul c
  have h := (homGenerator_hasDerivAt D e F x).scomp_of_eq 0 ht (by simp)
  have heq : (fun t : ℝ => F (coordinateExp D e (t • (c • x)))) =
      (fun t : ℝ => F (coordinateExp D e ((c*t) • x))) := by
    funext t
    rw [smul_smul,mul_comm t c]
  apply (homGenerator_hasDerivAt D e F (c • x)).unique
  rw [heq]
  exact h

/-- Generator addition is derived from the proved quadratic product
error and uniqueness of derivatives. It is not imposed on the generators. -/
theorem homGenerator_add (F : ContinuousMonoidHom G A) (x y : E) :
    homGenerator D e F (x+y) = homGenerator D e F x+homGenerator D e F y := by
  obtain ⟨K,δ,hK,hδ,herror⟩ := coordinateHom_add_error D e F
  let f := fun t : ℝ => F (coordinateExp D e (t • x))*F (coordinateExp D e (t • y))-
    F (coordinateExp D e (t • (x+y)))
  have hf0 : f 0 = 0 := by simp only [f,zero_smul,coordinateExp_zero,map_one,one_mul,sub_self]
  have hdx := homGenerator_hasDerivAt D e F x
  have hdy := homGenerator_hasDerivAt D e F y
  have hds := homGenerator_hasDerivAt D e F (x+y)
  have hd : HasDerivAt f (homGenerator D e F x+homGenerator D e F y-homGenerator D e F (x+y)) 0 := by
    have h := (hdx.mul hdy).sub hds
    change HasDerivAt f (homGenerator D e F x*F (coordinateExp D e ((0 : ℝ) • y))+
      F (coordinateExp D e ((0 : ℝ) • x))*homGenerator D e F y-homGenerator D e F (x+y)) 0 at h
    simpa only [zero_smul,coordinateExp_zero,map_one,mul_one,one_mul] using h
  have hxsmall : ∀ᶠ t : ℝ in 𝓝 0, ‖t • x‖ < δ := by
    have hc : ContinuousAt (fun t : ℝ => ‖t • x‖) 0 := (continuous_id.smul continuous_const).norm.continuousAt
    exact hc.preimage_mem_nhds (gt_mem_nhds (by simpa only [zero_smul,norm_zero] using hδ))
  have hysmall : ∀ᶠ t : ℝ in 𝓝 0, ‖t • y‖ < δ := by
    have hc : ContinuousAt (fun t : ℝ => ‖t • y‖) 0 := (continuous_id.smul continuous_const).norm.continuousAt
    exact hc.preimage_mem_nhds (gt_mem_nhds (by simpa only [zero_smul,norm_zero] using hδ))
  have hB : f =O[𝓝 (0 : ℝ)] (fun t : ℝ => ‖t‖^2) := by
    apply IsBigO.of_bound (K*‖x‖*‖y‖)
    filter_upwards [hxsmall,hysmall] with t ht₁ ht₂
    have h := herror (t • x) (t • y) ht₁ ht₂
    rw [← smul_add,norm_smul,norm_smul] at h
    change ‖f t‖ ≤ _ at h
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖t‖)]
    exact h.trans_eq (by ring)
  have hL := hB.trans_isLittleO (isLittleO_norm_pow_id (E' := ℝ) (by norm_num : 1 < 2))
  have hzero : HasDerivAt f 0 0 := by
    rw [hasDerivAt_iff_isLittleO]
    simpa only [hf0,sub_zero,smul_zero] using hL
  exact (sub_eq_zero.mp (hd.unique hzero)).symm

/-- The generators form an actual linear map. -/
noncomputable def homGeneratorLinear (F : ContinuousMonoidHom G A) : E →ₗ[ℝ] A where
  toFun := homGenerator D e F
  map_add' := homGenerator_add D e F
  map_smul' := homGenerator_smul D e F

end DirectedCycles.GleasonLieAlgebra
