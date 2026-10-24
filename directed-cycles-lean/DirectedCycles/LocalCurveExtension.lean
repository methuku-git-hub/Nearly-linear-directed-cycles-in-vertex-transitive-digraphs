import DirectedCycles.CompactNSSCurve

set_option autoImplicit false
namespace DirectedCycles
variable {H : Type*} [Group H]

/-- Iterating a local additive identity only uses partial sums in its given
real interval. -/
theorem local_curve_nat_mul (f : ℝ → H) (h0 : f 0 = 1) {r : ℝ}
    (hadd : ∀ s t : ℝ, |s|+|t| ≤ r → f (s+t) = f s*f t)
    (t : ℝ) (n : ℕ) (hn : (n : ℝ)*|t| ≤ r) : f ((n : ℝ)*t) = (f t)^n := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hprev : (n : ℝ)*|t| ≤ r := by
      push_cast at hn
      nlinarith [abs_nonneg t]
    rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,hadd,ih hprev,pow_succ]
    simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    push_cast at hn
    nlinarith

/-- Subdivision independence for a local one-parameter map. -/
theorem local_curve_refine (f : ℝ → H) (h0 : f 0 = 1) {r : ℝ}
    (hadd : ∀ s t : ℝ, |s|+|t| ≤ r → f (s+t) = f s*f t)
    (t : ℝ) (n m : ℕ) (hm : 0 < m) (hbound : |t/(n : ℝ)| ≤ r) :
    (f (t/(n : ℝ)))^n = (f (t/((n : ℝ)*(m : ℝ))))^(n*m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (m : ℝ)*(t/((n : ℝ)*(m : ℝ))) = t/(n : ℝ) := by
    rw [div_mul_eq_div_div]
    field_simp
  have hb : (m : ℝ)*|t/((n : ℝ)*(m : ℝ))| ≤ r := by
    calc
      (m : ℝ)*|t/((n : ℝ)*(m : ℝ))| = |(m : ℝ)*(t/((n : ℝ)*(m : ℝ)))| := by
        rw [abs_mul,abs_of_pos hmR]
      _ = |t/(n : ℝ)| := congrArg abs he
      _ ≤ r := hbound
  have hh := local_curve_nat_mul f h0 hadd (t/((n : ℝ)*(m : ℝ))) m hb
  rw [he] at hh
  rw [hh,← pow_mul,Nat.mul_comm m n]

/-- A local additive curve on a fixed interval extends algebraically to all
real parameters. All subdivision and commutation facts are derived from the
local identity. -/
theorem exists_local_curve_extension (f : ℝ → H) (h0 : f 0 = 1) {r : ℝ} (hr : 0 < r)
    (hadd : ∀ s t : ℝ, |s|+|t| ≤ r → f (s+t) = f s*f t) :
    ∃ F : ℝ → H, F 0 = 1 ∧ (∀ s t : ℝ, F (s+t) = F s*F t) ∧
      ∀ t : ℝ, |t| ≤ r → F t = f t := by
  have exists_scale : ∀ b : ℝ, ∃ n : ℕ, 0 < n ∧ b ≤ (n : ℝ)*r := by
    intro b
    obtain ⟨n,hn⟩ := exists_nat_gt (max (b/r) 0)
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
    refine ⟨n,by exact_mod_cast hn0,?_⟩
    have hbn : b/r < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    exact ((div_lt_iff₀ hr).1 hbn).le
  choose n hn hscale using fun t : ℝ => exists_scale |t|
  let F : ℝ → H := fun t => (f (t/(n t : ℝ)))^(n t)
  have hbound : ∀ t : ℝ, |t/(n t : ℝ)| ≤ r := by
    intro t
    have hnR : (0 : ℝ) < n t := by exact_mod_cast hn t
    rw [abs_div,abs_of_pos hnR]
    exact (div_le_iff₀ hnR).2 (by simpa only [mul_comm] using hscale t)
  have any_scale : ∀ t : ℝ, ∀ m : ℕ, 0 < m → |t/(m : ℝ)| ≤ r →
      F t = (f (t/(m : ℝ)))^m := by
    intro t m hm hbm
    dsimp only [F]
    rw [local_curve_refine f h0 hadd t (n t) m hm (hbound t),
      local_curve_refine f h0 hadd t m (n t) (hn t) hbm]
    simp only [mul_comm (n t : ℝ) (m : ℝ),Nat.mul_comm (n t) m]
  have hagree : ∀ t : ℝ, |t| ≤ r → F t = f t := by
    intro t ht
    simpa only [Nat.cast_one,div_one,pow_one] using any_scale t 1 (by omega) (by simpa using ht)
  refine ⟨F,(hagree 0 (by simpa using hr.le)).trans h0,?_,hagree⟩
  intro s t
  obtain ⟨m,hm,hbm⟩ := exists_scale (|s|+|t|)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hst : |s/(m : ℝ)|+|t/(m : ℝ)| ≤ r := by
    rw [abs_div,abs_div,abs_of_pos hmR,← add_div]
    exact (div_le_iff₀ hmR).2 (by simpa only [mul_comm] using hbm)
  have hs : |s/(m : ℝ)| ≤ r := by linarith [abs_nonneg (t/(m : ℝ))]
  have ht : |t/(m : ℝ)| ≤ r := by linarith [abs_nonneg (s/(m : ℝ))]
  have hsum : |(s+t)/(m : ℝ)| ≤ r := by
    rw [add_div]
    exact (abs_add_le _ _).trans hst
  rw [any_scale (s+t) m hm hsum,any_scale s m hm hs,any_scale t m hm ht,add_div,hadd _ _ hst]
  have hc : Commute (f (s/(m : ℝ))) (f (t/(m : ℝ))) := by
    change f (s/(m : ℝ))*f (t/(m : ℝ)) = f (t/(m : ℝ))*f (s/(m : ℝ))
    rw [← hadd _ _ hst,← hadd _ _ (by linarith : |t/(m : ℝ)|+|s/(m : ℝ)| ≤ r),add_comm]
  exact hc.mul_pow m
end DirectedCycles
