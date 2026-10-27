module

public import DirectedCycles.LocalMultiplicativeCurveSmooth
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Automatic smoothness of a continuous real multiplicative curve in a
Banach algebra. This uses only its actual algebra multiplication. -/
theorem normedAlgebra_one_parameter_contDiffAt_zero (φ : ℝ → A)
    (h0 : φ 0 = 1) (hc : ContinuousAt φ 0)
    (hm : ∀ s t, φ (s+t) = φ s*φ t) : ContDiffAt ℝ ∞ φ 0 := by
  let μ : A × A → A := fun p => (1+p.1)*(1+p.2)-1
  have hμ : ContDiffAt ℝ ∞ μ (0,0) :=
    ((contDiffAt_const.add contDiffAt_fst).mul (contDiffAt_const.add contDiffAt_snd)).sub contDiffAt_const
  have hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : A)] id := Filter.Eventually.of_forall (by
    intro x; simp [μ])
  have hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : A)] id := Filter.Eventually.of_forall (by
    intro x; simp [μ])
  let f := fun t => φ t-1
  have hf0 : f 0 = 0 := by simp [f,h0]
  have hfc : ContinuousAt f 0 := hc.sub continuousAt_const
  have hfm : ∀ s t : ℝ, |s|+|t| ≤ 1 → f (s+t) = μ (f s,f t) := by
    intro s t _hst
    simp only [f,μ,hm,← add_sub_assoc,add_sub_cancel_left]
  have h := local_multiplicative_curve_contDiffAt μ hμ hl hr f hf0 hfc
    (by norm_num : (0 : ℝ) < 1) hfm
  simpa only [f,sub_add_cancel] using h.add (contDiffAt_const (c := (1 : A)))

/-- The homomorphism law transports the constructed smoothness from zero
to every real parameter. -/
theorem normedAlgebra_one_parameter_contDiff (φ : ℝ → A)
    (h0 : φ 0 = 1) (hc : ContinuousAt φ 0)
    (hm : ∀ s t, φ (s+t) = φ s*φ t) : ContDiff ℝ ∞ φ := by
  have hz := normedAlgebra_one_parameter_contDiffAt_zero φ h0 hc hm
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hz' : ContDiffAt ℝ ∞ φ (x-x) := by simpa only [sub_self] using hz
  have hs : ContDiffAt ℝ ∞ (fun t => φ (t-x)) x := hz'.comp (f := fun t : ℝ => t-x) x (contDiffAt_id.sub contDiffAt_const)
  have h : ContDiffAt ℝ ∞ (fun t => φ x*φ (t-x)) x := contDiffAt_const.mul hs
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => by simpa only [add_sub_cancel] using hm x (t-x))

end DirectedCycles
