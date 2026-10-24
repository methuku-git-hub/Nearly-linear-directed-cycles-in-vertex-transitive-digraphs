import DirectedCycles.LieOneParameterExistence
import DirectedCycles.LieOneParameterUniqueness

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ,E) ∞ G]

/-- The constructed one-parameter subgroup with a prescribed coordinate
identity tangent. Uniqueness is proved separately, so the choice is immaterial. -/
noncomputable def lieOneParameter (v : E) : ℝ → G :=
  Classical.choose (lie_group_exists_one_parameter (G := G) v)

theorem lieOneParameter_zero (v : E) : lieOneParameter (G := G) v 0 = 1 :=
  (Classical.choose_spec (lie_group_exists_one_parameter (G := G) v)).1

theorem lieOneParameter_add (v : E) (s t : ℝ) :
    lieOneParameter (G := G) v (s+t) = lieOneParameter v s*lieOneParameter v t :=
  (Classical.choose_spec (lie_group_exists_one_parameter (G := G) v)).2.1 s t

theorem lieOneParameter_smooth (v : E) : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ (lieOneParameter (G := G) v) :=
  (Classical.choose_spec (lie_group_exists_one_parameter (G := G) v)).2.2.1

theorem lieOneParameter_derivative (v : E) :
    HasDerivAt (fun t => (chartAt E (1 : G)) (lieOneParameter v t)-(chartAt E (1 : G)) 1) v 0 :=
  (Classical.choose_spec (lie_group_exists_one_parameter (G := G) v)).2.2.2

/-- Scaling a tangent is exactly rescaling its constructed group curve. -/
theorem lieOneParameter_scaling (v : E) (s t : ℝ) :
    lieOneParameter (G := G) (s • v) t = lieOneParameter v (s*t) := by
  let φ : ℝ → G := fun a => lieOneParameter v (s*a)
  have hφ0 : φ 0 = 1 := by simp only [φ,mul_zero,lieOneParameter_zero]
  have hφadd : ∀ a b : ℝ, φ (a+b) = φ a*φ b := by
    intro a b
    simp only [φ,mul_add,lieOneParameter_add]
  have hφc : ContinuousAt φ 0 :=
    ((lieOneParameter_smooth (G := G) v).continuous.comp (continuous_const.mul continuous_id)).continuousAt
  have hscale : HasDerivAt (fun a : ℝ => s*a) s 0 := by
    simpa only [mul_one,id_eq] using (hasDerivAt_id (0 : ℝ)).const_mul s
  have hφv : HasDerivAt (fun a => (chartAt E (1 : G)) (φ a)-(chartAt E (1 : G)) 1) (s • v) 0 := by
    have hd := (lieOneParameter_derivative (G := G) v).scomp_of_eq 0 hscale (by simp only [mul_zero])
    simpa only [φ,Function.comp_def] using hd
  have he := lie_group_one_parameter_unique (lieOneParameter (G := G) (s • v)) φ
    (lieOneParameter_zero _) hφ0 (lieOneParameter_smooth _).continuous.continuousAt hφc
    (lieOneParameter_add _) hφadd (lieOneParameter_derivative _) hφv
  exact congrFun he t

/-- The actual Lie exponential in identity-chart tangent coordinates. -/
noncomputable def lieExponential (v : E) : G := lieOneParameter v 1

theorem lieExponential_smul (v : E) (t : ℝ) :
    lieExponential (G := G) (t • v) = lieOneParameter v t := by
  simpa only [lieExponential,mul_one] using lieOneParameter_scaling (G := G) v t 1

theorem lieExponential_zero : lieExponential (G := G) (0 : E) = 1 := by
  have h := lieExponential_smul (G := G) (0 : E) 0
  simpa only [zero_smul,lieOneParameter_zero] using h

theorem lieExponential_add_line (v : E) (s t : ℝ) :
    lieExponential (G := G) ((s+t) • v) = lieExponential (s • v)*lieExponential (t • v) := by
  simp only [lieExponential_smul,lieOneParameter_add]

theorem lieExponential_line_smooth (v : E) :
    ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ (fun t : ℝ => lieExponential (G := G) (t • v)) := by
  simpa only [lieExponential_smul] using lieOneParameter_smooth (G := G) v

/-- Every continuous one-parameter subgroup is the exponential of its actual
identity-coordinate tangent. -/
theorem lie_one_parameter_eq_exponential (φ : ℝ → G) (hφ0 : φ 0 = 1)
    (hφc : ContinuousAt φ 0) (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t)
    {v : E} (hφv : HasDerivAt (fun t => (chartAt E (1 : G)) (φ t)-(chartAt E (1 : G)) 1) v 0) :
    ∀ t : ℝ, φ t = lieExponential (G := G) (t • v) := by
  have he := lie_group_one_parameter_unique φ (lieOneParameter (G := G) v) hφ0
    (lieOneParameter_zero _) hφc (lieOneParameter_smooth _).continuous.continuousAt hφadd
    (lieOneParameter_add _) hφv (lieOneParameter_derivative _)
  intro t
  rw [lieExponential_smul]
  exact congrFun he t
end DirectedCycles
