module

public import DirectedCycles.LocalCurveExtension
public import Mathlib.Topology.Instances.RealVectorSpace

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous local additive real curve is the restriction of a real
linear map. Subdivision proves the extension, so no global additive identity
is assumed at the source. -/
theorem local_additive_curve_linear (g : ℝ → E) (h0 : g 0 = 0)
    (hcont : ContinuousAt g 0) {r : ℝ} (hr : 0 < r)
    (hadd : ∀ s t : ℝ, |s|+|t| ≤ r → g (s+t) = g s+g t) :
    ∃ v : E, ∀ t : ℝ, |t| ≤ r → g t = t • v := by
  have h0' : Multiplicative.ofAdd (g 0) = (1 : Multiplicative E) := congrArg Multiplicative.ofAdd h0
  have hadd' : ∀ s t : ℝ, |s|+|t| ≤ r →
      Multiplicative.ofAdd (g (s+t)) = Multiplicative.ofAdd (g s)*Multiplicative.ofAdd (g t) :=
    fun s t ht => congrArg Multiplicative.ofAdd (hadd s t ht)
  obtain ⟨F,hF0,hFadd,hagree⟩ := exists_local_curve_extension (fun t => Multiplicative.ofAdd (g t)) h0' hr hadd'
  let A : ℝ →+ E := {
    toFun := fun t => (F t).toAdd
    map_zero' := congrArg Multiplicative.toAdd hF0
    map_add' := fun s t => congrArg Multiplicative.toAdd (hFadd s t) }
  have hAg : ∀ t : ℝ, |t| ≤ r → A t = g t := fun t ht => congrArg Multiplicative.toAdd (hagree t ht)
  have hnear : g =ᶠ[𝓝 (0 : ℝ)] A := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
    have hh : |t| < r := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht
    exact (hAg t hh.le).symm
  have hlim : Filter.Tendsto g (𝓝 (0 : ℝ)) (𝓝 0) := by simpa only [h0] using hcont.tendsto
  have hAc : Continuous A := continuous_of_tendsto_nhds_zero A (hlim.congr' hnear)
  refine ⟨A 1,?_⟩
  intro t ht
  rw [← hAg t ht]
  have hh := (A.toRealLinearMap hAc).map_smul t (1 : ℝ)
  change A (t*(1 : ℝ)) = t • A 1 at hh
  simpa only [mul_one] using hh
end DirectedCycles
