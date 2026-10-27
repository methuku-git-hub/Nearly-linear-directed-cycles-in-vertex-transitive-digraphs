module

public import DirectedCycles.GleasonTrotterParameterLaws

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace OneParameter
variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Scalar reparameterisation of an actual one-parameter subgroup. -/
noncomputable def scale (c : ℝ) (φ : OneParameter G) : OneParameter G where
  toFun x := φ.eval (c*x.toAdd)
  map_one' := by simp
  map_mul' x y := by change φ.eval (c*(x.toAdd+y.toAdd)) = _; rw [mul_add,φ.eval_add]
  continuous_toFun := φ.continuous_eval.comp (continuous_const.mul continuous_id)

@[simp] theorem scale_eval (c : ℝ) (φ : OneParameter G) (t : ℝ) :
    (scale c φ).eval t = φ.eval (c*t) := rfl

@[simp] theorem one_eval (t : ℝ) : (1 : OneParameter G).eval t = 1 := rfl

theorem scale_zero (φ : OneParameter G) : scale 0 φ = 1 := by
  apply ContinuousMonoidHom.ext
  intro x
  change φ.eval (0*x.toAdd) = 1
  simp

theorem scale_one (φ : OneParameter G) : scale 1 φ = φ := by
  apply ContinuousMonoidHom.ext
  intro x
  change φ.eval (1*x.toAdd) = φ.eval x.toAdd
  rw [one_mul]

theorem scale_mul (a b : ℝ) (φ : OneParameter G) :
    scale a (scale b φ) = scale (a*b) φ := by
  apply ContinuousMonoidHom.ext
  intro x
  change φ.eval (b*(a*x.toAdd)) = φ.eval ((a*b)*x.toAdd)
  congr 1
  ring

theorem productApprox_scale (c : ℝ) (φ ψ : OneParameter G) (t : ℝ) (n : ℕ) :
    (scale c φ).productApprox (scale c ψ) t n = φ.productApprox ψ (c*t) n := by
  simp only [productApprox,scale_eval,mul_div_assoc]

theorem productApprox_one (φ : OneParameter G) (t : ℝ) (n : ℕ) (hn : 0 < n) :
    φ.productApprox 1 t n = φ.eval t := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [productApprox,one_eval,mul_one,← φ.eval_nat_mul,mul_div_cancel₀ _ (ne_of_gt hnR)]

theorem productApprox_same_scales (a b : ℝ) (φ : OneParameter G) (t : ℝ) (n : ℕ) (hn : 0 < n) :
    (scale a φ).productApprox (scale b φ) t n = (scale (a+b) φ).eval t := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [productApprox,scale_eval,← φ.eval_add,← φ.eval_nat_mul]
  congr 1
  field_simp

theorem productApprox_swap (φ ψ : OneParameter G) (t : ℝ) (n : ℕ) :
    ψ.productApprox φ t n = ψ.eval (t/(n : ℝ))*φ.productApprox ψ t n*(ψ.eval (t/(n : ℝ)))⁻¹ := by
  have hc : ψ.eval (t/(n : ℝ))*φ.eval (t/(n : ℝ)) =
      ψ.eval (t/(n : ℝ))*(φ.eval (t/(n : ℝ))*ψ.eval (t/(n : ℝ)))*(ψ.eval (t/(n : ℝ)))⁻¹ := by group
  dsimp only [productApprox]
  rw [hc]
  exact conj_pow
end OneParameter
end DirectedCycles
