module

public import DirectedCycles.LocalMultiplicativeGermUniqueness

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform local multiplication curves obey parameter scaling on their
common interval. The proof compares their actual tangents and local laws. -/
theorem uniform_local_curve_scaling (μ : E × E → E) (hμ : ContDiffAt ℝ 2 μ (0,0))
    (f : E × ℝ → E) {R r : ℝ} (hr : 0 < r)
    (hfinit : ∀ v : E, ‖v‖ < R → f (v,0) = 0 ∧ HasDerivAt (fun t => f (v,t)) v 0)
    (hflaw : ∀ v : E, ‖v‖ < R → ∀ a b : ℝ, |a|+|b| ≤ r →
      f (v,a+b) = μ (f (v,a),f (v,b)))
    (v : E) (hv : ‖v‖ < R) (s : ℝ) (hs : |s| ≤ 1) (t : ℝ) (ht : |t| ≤ r) :
    f (s • v,t) = f (v,s*t) := by
  have hsv : ‖s • v‖ < R := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hs (norm_nonneg v)).trans_lt (by simpa only [one_mul] using hv)
  obtain ⟨hf0,hfv⟩ := hfinit v hv
  obtain ⟨hfs0,hfsv⟩ := hfinit (s • v) hsv
  have hscale : HasDerivAt (fun a : ℝ => s*a) s 0 := by
    simpa only [mul_one,id_eq] using (hasDerivAt_id (0 : ℝ)).const_mul s
  have hgv : HasDerivAt (fun a => f (v,s*a)) (s • v) 0 := by
    simpa only [Function.comp_def] using hfv.scomp_of_eq 0 hscale (by simp only [mul_zero])
  have hglaw : ∀ a b : ℝ, |a|+|b| ≤ r → f (v,s*(a+b)) = μ (f (v,s*a),f (v,s*b)) := by
    intro a b hab
    rw [mul_add]
    apply hflaw v hv
    rw [abs_mul,abs_mul,← mul_add]
    exact (mul_le_mul_of_nonneg_right hs (add_nonneg (abs_nonneg a) (abs_nonneg b))).trans
      (by simpa only [one_mul] using hab)
  exact local_multiplicative_curve_unique μ hμ (fun a => f (s • v,a)) (fun a => f (v,s*a))
    hfs0 (by simpa only [mul_zero] using hf0) hfsv hgv hr hr (hflaw (s • v) hsv) hglaw t ht ht
end DirectedCycles
