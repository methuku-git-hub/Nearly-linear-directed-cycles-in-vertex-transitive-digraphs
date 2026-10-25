module

public import DirectedCycles.GleasonLieAlgebraFunctor

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation as an actual continuous group homomorphism. -/
def continuousConjugation (g : G) : ContinuousMonoidHom G G where
  toFun x := g*x*g⁻¹
  map_one' := by simp
  map_mul' x y := by group
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const

theorem continuousConjugation_one : continuousConjugation (1 : G) = ContinuousMonoidHom.id G := by
  ext x
  change 1*x*1⁻¹ = x
  simp

theorem continuousConjugation_mul (g h : G) :
    continuousConjugation (g*h) = (continuousConjugation g).comp (continuousConjugation h) := by
  ext x
  change (g*h)*x*(g*h)⁻¹ = g*(h*x*h⁻¹)*g⁻¹
  group

namespace GleasonLieAlgebra
variable (D : GleasonMetricData G) [LocallyCompactSpace G]

/-- The actual adjoint representation on the constructed vector space. -/
noncomputable def adjoint (g : G) : GleasonLieAlgebra D →L[ℝ] GleasonLieAlgebra D :=
  map D D (continuousConjugation g)

theorem adjoint_eval (g : G) (x : GleasonLieAlgebra D) (t : ℝ) :
    (toOneParameter D (adjoint D g x)).eval t = g*(toOneParameter D x).eval t*g⁻¹ := rfl

theorem exp_adjoint (g : G) (x : GleasonLieAlgebra D) :
    exp D (adjoint D g x) = g*exp D x*g⁻¹ := rfl

theorem adjoint_one : adjoint D (1 : G) = ContinuousLinearMap.id ℝ (GleasonLieAlgebra D) := by
  rw [adjoint,continuousConjugation_one,map_id]

theorem adjoint_mul (g h : G) : adjoint D (g*h) = (adjoint D g).comp (adjoint D h) := by
  exact (congrArg (map D D) (continuousConjugation_mul g h)).trans (map_comp D D D _ _)

/-- Joint continuity holds in the original compact-open vector topology. -/
theorem continuous_adjoint_apply :
    Continuous (fun p : G × GleasonLieAlgebra D => adjoint D p.1 p.2) := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous (fun p : (G × GleasonLieAlgebra D) × Multiplicative ℝ =>
    p.1.1*(toOneParameter D p.1.2).eval p.2.toAdd*p.1.1⁻¹)
  have he : Continuous (fun p : (G × GleasonLieAlgebra D) × Multiplicative ℝ =>
    (toOneParameter D p.1.2).eval p.2.toAdd) :=
    OneParameter.continuous_eval_pair.comp
      (((toOneParameter D).continuous.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
  exact ((continuous_fst.comp continuous_fst).mul he).mul (continuous_fst.comp continuous_fst).inv
end GleasonLieAlgebra
end DirectedCycles
