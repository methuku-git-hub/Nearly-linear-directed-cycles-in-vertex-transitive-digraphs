import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sequences
import Mathlib.Tactic

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- Natural power compatibility and inversion give integer compatibility
on the same local interval. -/
theorem local_curve_int_mul_of_power (F : ℝ → G) {T : ℝ} (h0 : F 0 = 1)
    (hpow : ∀ t : ℝ, ∀ n : ℕ, 0 < n → |t| ≤ T → |(n : ℝ)*t| ≤ T → F ((n : ℝ)*t) = (F t)^n)
    (hinv : ∀ t : ℝ, |t| ≤ T → F (-t) = (F t)⁻¹)
    (t : ℝ) (z : ℤ) (ht : |t| ≤ T) (hzt : |(z : ℝ)*t| ≤ T) :
    F ((z : ℝ)*t) = (F t)^z := by
  cases z with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast,Int.cast_natCast,zpow_natCast] at hzt ⊢
    by_cases hn : n = 0
    · subst n
      simpa only [Nat.cast_zero,zero_mul,pow_zero] using h0
    · exact hpow t n (by omega) ht hzt
  | negSucc n =>
    have hnt : |((n+1 : ℕ) : ℝ)*t| ≤ T := by
      simpa only [Int.cast_negSucc,neg_mul,abs_neg,Nat.cast_add,Nat.cast_one] using hzt
    rw [Int.cast_negSucc,neg_mul,hinv _ hnt]
    rw [hpow t (n+1) (by omega) ht hnt]
    simp only [zpow_negSucc]

/-- On a common rational subdivision, the local addition law is an exact
identity of integer powers. -/
theorem local_curve_rat_add_of_power (F : ℝ → G) {T : ℝ} (hT : 0 < T) (h0 : F 0 = 1)
    (hpow : ∀ t : ℝ, ∀ n : ℕ, 0 < n → |t| ≤ T → |(n : ℝ)*t| ≤ T → F ((n : ℝ)*t) = (F t)^n)
    (hinv : ∀ t : ℝ, |t| ≤ T → F (-t) = (F t)⁻¹)
    (q p : ℚ) (hqp : |T*(q : ℝ)|+|T*(p : ℝ)| ≤ T) :
    F (T*(q : ℝ)+T*(p : ℝ)) = F (T*(q : ℝ))*F (T*(p : ℝ)) := by
  let d : ℕ := q.den*p.den
  have hd : 0 < d := Nat.mul_pos q.den_pos p.den_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  let a : ℤ := q.num*(p.den : ℤ)
  let b : ℤ := p.num*(q.den : ℤ)
  let x : ℝ := T/(d : ℝ)
  have hx : |x| ≤ T := by
    rw [abs_of_pos (show 0 < x by dsimp [x]; positivity)]
    apply (div_le_iff₀ hdR).mpr
    nlinarith
  have hq : (a : ℝ)*x = T*(q : ℝ) := by
    dsimp [a,x,d]
    rw [Rat.cast_def]
    push_cast
    field_simp
  have hp : (b : ℝ)*x = T*(p : ℝ) := by
    dsimp [b,x,d]
    rw [Rat.cast_def]
    push_cast
    field_simp
  have hsum : ((a+b : ℤ) : ℝ)*x = T*(q : ℝ)+T*(p : ℝ) := by
    rw [Int.cast_add,add_mul,hq,hp]
  have hqa : |(a : ℝ)*x| ≤ T := by rw [hq]; linarith [abs_nonneg (T*(p : ℝ))]
  have hpb : |(b : ℝ)*x| ≤ T := by rw [hp]; linarith [abs_nonneg (T*(q : ℝ))]
  have hab : |((a+b : ℤ) : ℝ)*x| ≤ T := by rw [hsum]; exact (abs_add_le _ _).trans hqp
  rw [← hsum,← hq,← hp,local_curve_int_mul_of_power F h0 hpow hinv x (a+b) hx hab,
    local_curve_int_mul_of_power F h0 hpow hinv x a hx hqa,
    local_curve_int_mul_of_power F h0 hpow hinv x b hx hpb,zpow_add]

/-- Continuity upgrades exact rational subdivision identities to the local
addition law on a smaller closed interval. -/
theorem local_curve_add_of_power [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (F : ℝ → G) {T : ℝ} (hT : 0 < T) (h0 : F 0 = 1)
    (hc : ContinuousOn F {t : ℝ | |t| ≤ T})
    (hpow : ∀ t : ℝ, ∀ n : ℕ, 0 < n → |t| ≤ T → |(n : ℝ)*t| ≤ T → F ((n : ℝ)*t) = (F t)^n)
    (hinv : ∀ t : ℝ, |t| ≤ T → F (-t) = (F t)⁻¹)
    (s t : ℝ) (hst : |s|+|t| ≤ T/2) : F (s+t) = F s*F t := by
  obtain ⟨q,_hqmono,_hqlt,hq⟩ := Real.exists_seq_rat_strictMono_tendsto (s/T)
  obtain ⟨p,_hpmono,_hplt,hp⟩ := Real.exists_seq_rat_strictMono_tendsto (t/T)
  let u : ℕ → ℝ := fun n => T*(q n : ℝ)
  let v : ℕ → ℝ := fun n => T*(p n : ℝ)
  have hu : Tendsto u atTop (𝓝 s) := by
    simpa only [mul_div_cancel₀ _ (ne_of_gt hT)] using (tendsto_const_nhds (x := T)).mul hq
  have hv : Tendsto v atTop (𝓝 t) := by
    simpa only [mul_div_cancel₀ _ (ne_of_gt hT)] using (tendsto_const_nhds (x := T)).mul hp
  have hsumsmall : |s|+|t| < T := by linarith
  have hev : ∀ᶠ n in atTop, |u n|+|v n| ≤ T :=
    ((hu.abs.add hv.abs).eventually (gt_mem_nhds hsumsmall)).mono fun _ h => h.le
  have hs : |s| ≤ T := by linarith [abs_nonneg t]
  have ht : |t| ≤ T := by linarith [abs_nonneg s]
  have hsum : |s+t| ≤ T := (abs_add_le _ _).trans hsumsmall.le
  have hFu : Tendsto (fun n => F (u n)) atTop (𝓝 (F s)) := by
    apply (hc s hs).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hu,?_⟩
    filter_upwards [hev] with n hn
    linarith [abs_nonneg (v n)]
  have hFv : Tendsto (fun n => F (v n)) atTop (𝓝 (F t)) := by
    apply (hc t ht).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hv,?_⟩
    filter_upwards [hev] with n hn
    linarith [abs_nonneg (u n)]
  have hFsum : Tendsto (fun n => F (u n+v n)) atTop (𝓝 (F (s+t))) := by
    apply (hc (s+t) hsum).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hu.add hv,?_⟩
    filter_upwards [hev] with n hn
    exact (abs_add_le _ _).trans hn
  have he : (fun n => F (u n+v n)) =ᶠ[atTop] (fun n => F (u n)*F (v n)) := by
    filter_upwards [hev] with n hn
    exact local_curve_rat_add_of_power F hT h0 hpow hinv (q n) (p n) hn
  exact tendsto_nhds_unique hFsum ((hFu.mul hFv).congr' he.symm)
end DirectedCycles
