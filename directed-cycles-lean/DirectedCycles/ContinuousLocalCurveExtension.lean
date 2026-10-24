import DirectedCycles.LocalCurveExtension
import DirectedCycles.GleasonOneParameter
import Mathlib.Topology.Algebra.Group.Neighborhood

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The algebraic extension of a locally additive curve is an actual
continuous one-parameter homomorphism when the original curve is continuous
at zero. -/
theorem exists_continuous_local_curve_extension (f : ℝ → G) (h0 : f 0 = 1)
    (hc : ContinuousAt f 0) {r : ℝ} (hr : 0 < r)
    (hadd : ∀ s t : ℝ, |s|+|t| ≤ r → f (s+t) = f s*f t) :
    ∃ φ : OneParameter G, ∀ t : ℝ, |t| ≤ r → φ.eval t = f t := by
  obtain ⟨F,hF0,hFadd,hagree⟩ := exists_local_curve_extension f h0 hr hadd
  have heq : F =ᶠ[𝓝 (0 : ℝ)] f := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
    exact hagree t (le_of_lt (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht))
  have hFcont : ContinuousAt F 0 := hc.congr_of_eventuallyEq heq
  let H : Multiplicative ℝ →* G := {
    toFun := fun x => F x.toAdd
    map_one' := hF0
    map_mul' := fun x y => hFadd x.toAdd y.toAdd }
  have hH : Continuous H := continuous_of_continuousAt_one H hFcont
  exact ⟨{ H with continuous_toFun := hH },hagree⟩

omit [IsTopologicalGroup G] in
/-- Agreement on any positive interval determines a global one-parameter
homomorphism by finite subdivision. -/
theorem OneParameter.eq_of_local_eq (φ ψ : OneParameter G) {r : ℝ} (hr : 0 < r)
    (h : ∀ t : ℝ, |t| ≤ r → φ.eval t = ψ.eval t) : φ = ψ := by
  apply ContinuousMonoidHom.ext
  intro x
  obtain ⟨n,hn⟩ := exists_nat_gt (|x.toAdd|/r)
  have hnR : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (abs_nonneg _) hr.le) hn
  have hsmall : |x.toAdd/(n : ℝ)| ≤ r := by
    rw [abs_div,abs_of_pos hnR]
    apply (div_le_iff₀ hnR).mpr
    nlinarith [(div_lt_iff₀ hr).mp hn]
  have he := congrArg (fun g : G => g^n) (h _ hsmall)
  rw [← φ.eval_nat_mul,← ψ.eval_nat_mul,mul_div_cancel₀ _ (ne_of_gt hnR)] at he
  exact he
end DirectedCycles
