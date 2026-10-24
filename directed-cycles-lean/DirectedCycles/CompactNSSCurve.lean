import DirectedCycles.CompactPowerTrapping
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] in
theorem real_additive_curve_nat_mul (f : ℝ → G) (h0 : f 0 = 1)
    (hadd : ∀ s t, f (s+t) = f s*f t) (t : ℝ) (n : ℕ) : f ((n : ℝ)*t) = (f t)^n := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,hadd,ih,pow_succ]

/-- An algebraic one-parameter map with a bounded interval in a compact NSS
region is continuous. Compactness supplies the finite-power trapping needed
at zero, and the homomorphism identity gives continuity everywhere. -/
theorem continuous_curve_of_compact_nss (f : ℝ → G) (h0 : f 0 = 1)
    (hadd : ∀ s t, f (s+t) = f s*f t)
    {V : Set G} (hV : IsCompact V)
    (hNSS : ∀ x : G, (∀ n : ℕ, x^n ∈ V) → x = 1)
    {r : ℝ} (hr : 0 < r) (hbound : ∀ t : ℝ, |t| ≤ r → f t ∈ V) : Continuous f := by
  have hcont0 : Filter.Tendsto f (𝓝 (0 : ℝ)) (𝓝 (1 : G)) := by
    apply Filter.tendsto_def.2
    intro S hS
    obtain ⟨W,hWS,hWo,hW1⟩ := mem_nhds_iff.mp hS
    obtain ⟨M,hM,htrap⟩ := compact_power_trapping hV hNSS hWo hW1
    have hMr : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hM)
    apply Metric.mem_nhds_iff.2
    refine ⟨r/(M : ℝ),div_pos hr hMr,?_⟩
    intro t ht
    have ht' : |t| < r/(M : ℝ) := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht
    apply hWS
    apply htrap (f t)
    intro n hn
    rw [← real_additive_curve_nat_mul f h0 hadd t n]
    apply hbound
    have hnr : (n : ℝ) ≤ M := by exact_mod_cast hn
    have htM : |t| *(M : ℝ) < r := (lt_div_iff₀ hMr).1 ht'
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
    have hscale := mul_le_mul_of_nonneg_right hnr (abs_nonneg t)
    nlinarith
  apply continuous_iff_continuousAt.2
  intro x
  change Filter.Tendsto f (𝓝 x) (𝓝 (f x))
  have hsub : Filter.Tendsto (fun t : ℝ => t-x) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t-x) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto x
  have hlim := Filter.Tendsto.mul ((continuous_const : Continuous (fun _ : ℝ => f x)).tendsto x) (hcont0.comp hsub)
  have heq : (fun t : ℝ => f x*f (t-x)) =ᶠ[𝓝 x] f := Filter.Eventually.of_forall fun t => by
    simpa only [add_sub_cancel] using (hadd x (t-x)).symm
  have hlim' := Filter.Tendsto.congr' heq hlim
  simpa only [mul_one] using hlim'
end DirectedCycles
