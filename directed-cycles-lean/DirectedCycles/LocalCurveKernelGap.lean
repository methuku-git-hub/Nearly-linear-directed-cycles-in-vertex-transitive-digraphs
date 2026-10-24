import DirectedCycles.LocalRelationCurveGermUniqueness
import DirectedCycles.LocalGlobalSubgroup
import DirectedCycles.LocalGroupReversal

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {H : Type*} (Q : LocalGroupAlgebra H)

/-- Excluding complete power sequences excludes every actual global subgroup,
without any finiteness hypothesis on the local ambient group. -/
theorem local_isNSS_of_powerSequence (V : Set H)
    (hNSS : ∀ x : H, ∀ p : Q.PowerSequence x, (∀ n, p.power n ∈ V) → x = Q.one) :
    Q.IsNSS V := by
  intro S hS hSV x hx
  let := hS.toGroup
  let xS : S := ⟨x,hx⟩
  let p : Q.PowerSequence x := {
    power := fun n => ((xS^n : S) : H)
    product := by
      intro n
      have hp := (LocalGroupAlgebra.ofGroup_product S (List.replicate n xS)).map hS.inclusionHom
      simpa [LocalGroupAlgebra.IsGlobalSubgroup.inclusionHom,xS] using hp }
  exact hNSS x p (fun n => hSV (xS^n).property)

/-- Inverse parameters follow from the actual half-parameter products, so the
law is used only inside its prescribed unit interval. -/
theorem local_curve_inverse (hr : Q.Reversible) (f : ℝ → H) (hf0 : f 0 = Q.one)
    (hadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t)))
    {t : ℝ} (ht : |t| ≤ 1) : f (-t) = Q.inv (f t) := by
  have habs : |t/2| = |t|/2 := by rw [abs_div]; norm_num
  have hi := hadd (t/2) (-(t/2)) (by rw [abs_neg,habs]; linarith)
  rw [add_neg_cancel,hf0] at hi
  have hneg := Q.right_inverse_unique hi
  have hp := hadd (t/2) (t/2) (by rw [habs]; linarith)
  have hn := hadd (-(t/2)) (-(t/2)) (by rw [abs_neg,habs]; linarith)
  have hsum : t/2+t/2 = t := by ring
  have hnsum : -(t/2)+-(t/2) = -t := by ring
  rw [hsum] at hp
  rw [hnsum,hneg] at hn
  exact Q.unique hn (hr hp)

/-- A returning positive local curve segment, with all its binary products
actually defined, is a genuine global subgroup. -/
theorem local_curve_period_isGlobalSubgroup (f : ℝ → H) (hf0 : f 0 = Q.one)
    (hadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t)))
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hperiod : f r = Q.one)
    (hdom : ∀ s ∈ Set.Icc (0 : ℝ) r, ∀ t ∈ Set.Icc (0 : ℝ) r, Q.Defined (f s) (f t)) :
    Q.IsGlobalSubgroup (f '' Set.Icc (0 : ℝ) r) where
  one_mem := ⟨0,⟨le_rfl,hr.le⟩,hf0⟩
  inv_mem := by
    rintro _ ⟨s,hs,rfl⟩
    have hh := hadd s (r-s) (by rw [abs_of_nonneg hs.1,abs_of_nonneg (sub_nonneg.2 hs.2)]; linarith)
    rw [add_sub_cancel,hperiod] at hh
    exact ⟨r-s,⟨by linarith [hs.2],by linarith [hs.1]⟩,Q.right_inverse_unique hh⟩
  mul_total := by
    rintro _ ⟨s,hs,rfl⟩ _ ⟨t,ht,rfl⟩
    by_cases hst : s+t ≤ r
    · exact ⟨f (s+t),⟨s+t,⟨by linarith [hs.1,ht.1],hst⟩,rfl⟩,
        hadd s t (by rw [abs_of_nonneg hs.1,abs_of_nonneg ht.1]; exact hst.trans hr1)⟩
    · have hv : 0 ≤ s+t-r := by linarith
      have hvr : s+t-r ≤ r := by linarith [hs.2,ht.2]
      have hA := hadd s (r-s) (by rw [abs_of_nonneg hs.1,abs_of_nonneg (sub_nonneg.2 hs.2)]; linarith)
      rw [add_sub_cancel,hperiod] at hA
      have hB := hadd (r-s) (s+t-r) (by
        rw [abs_of_nonneg (sub_nonneg.2 hs.2),abs_of_nonneg hv]
        linarith [ht.2])
      have hb : r-s+(s+t-r) = t := by ring
      rw [hb] at hB
      obtain ⟨z,hz⟩ := hdom s hs t ht
      have he : f (s+t-r) = z := Q.assoc hA hB (Q.one_mul _) hz
      exact ⟨z,⟨s+t-r,⟨hv,hvr⟩,he⟩,hz⟩

/-- NSS excludes nonzero kernel parameters throughout the closed local curve
segment. The proof uses actual source-induced binary domains, never an
unproved extension to a global one-parameter group. -/
theorem local_curve_kernel_gap (hrQ : Q.Reversible) (f : ℝ → H) (hf0 : f 0 = Q.one)
    (hadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t)))
    (hf1 : f 1 ≠ Q.one) (V : Set H)
    (hNSS : ∀ x : H, ∀ p : Q.PowerSequence x, (∀ n, p.power n ∈ V) → x = Q.one)
    (hbound : ∀ t : ℝ, |t| ≤ 1 → f t ∈ V)
    (hdom : ∀ s t : ℝ, |s| ≤ 1 → |t| ≤ 1 → Q.Defined (f s) (f t))
    {t : ℝ} (ht : 0 < |t|) (ht1 : |t| ≤ 1) : f t ≠ Q.one := by
  intro hperiod
  have habs : f |t| = Q.one := by
    by_cases ht0 : 0 ≤ t
    · simpa only [abs_of_nonneg ht0] using hperiod
    · rw [abs_of_neg (lt_of_not_ge ht0),local_curve_inverse Q hrQ f hf0 hadd ht1,hperiod,Q.inv_one]
  have hg := local_curve_period_isGlobalSubgroup Q f hf0 hadd ht ht1 habs
    (fun s hs u hu => hdom s u (by rw [abs_of_nonneg hs.1]; exact hs.2.trans ht1)
      (by rw [abs_of_nonneg hu.1]; exact hu.2.trans ht1))
  have htrivial : ∀ s ∈ Set.Icc (0 : ℝ) |t|, f s = Q.one := by
    intro s hs
    apply local_isNSS_of_powerSequence Q V hNSS _ hg _ ⟨s,hs,rfl⟩
    rintro _ ⟨u,hu,rfl⟩
    exact hbound u (by rw [abs_of_nonneg hu.1]; exact hu.2.trans ht1)
  have heq : f =ᶠ[𝓝 (0 : ℝ)] (fun _ => Q.one) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min ht (by norm_num : (0 : ℝ)<1))] with s hs
    have hs' : |s| < min |t| 1 := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hs
    by_cases hs0 : 0 ≤ s
    · exact htrivial s ⟨hs0,by rw [abs_of_nonneg hs0] at hs'; exact hs'.le.trans (min_le_left _ _)⟩
    · have hm : f (-s) = Q.one := htrivial (-s) ⟨by linarith,by
        rw [abs_of_neg (lt_of_not_ge hs0)] at hs'
        exact hs'.le.trans (min_le_left _ _)⟩
      have hi := local_curve_inverse Q hrQ f hf0 hadd (hs'.le.trans (min_le_right _ _))
      rw [hm] at hi
      have hh := congrArg Q.inv hi
      simpa only [Q.inv_one,Q.inv_inv] using hh.symm
  apply hf1
  exact local_relation_curve_eq_of_eventually_eq Q f (fun _ => Q.one) hf0 hadd
    (r := 1) (s := 1) (fun _ _ _ => Q.one_mul Q.one) heq 1 (by norm_num) (by norm_num)
end DirectedCycles
