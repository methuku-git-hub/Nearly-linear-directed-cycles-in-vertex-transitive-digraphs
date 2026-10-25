module

public import DirectedCycles.Thresholds
public import Mathlib.Data.Nat.Find

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The last radius where a finite growth function exceeds a polynomial
has a bounded tripling ratio, above any prescribed starting radius. -/
theorem polynomial_crossing_scale (f : ℕ → ℕ) (n N d q : ℕ)
    (hf : ∀ t, 1 ≤ f t ∧ f t ≤ n) (hN : 1 ≤ N) (hd : 1 ≤ d) (hq : 2 ≤ q) :
    ∃ m : ℕ, N ≤ m ∧ m^d ≤ N^d*n ∧ f (q*m) ≤ q^d*f m := by
  classical
  have hpow : ∀ t : ℕ, t ≤ t^d := fun t => Nat.le_self_pow (by omega) t
  let P := fun t : ℕ => t^d ≤ N^d*f t
  let bound := N^d*n
  have hPb : ∀ t, P t → t ≤ bound := by
    intro t ht
    exact (hpow t).trans (ht.trans (Nat.mul_le_mul_left _ (hf t).2))
  have hPN : P N := by
    dsimp [P]
    exact Nat.le_mul_of_pos_right _ (by have := (hf N).1; omega : 0 < f N)
  let m := Nat.findGreatest P bound
  have hNm : N ≤ m := Nat.le_findGreatest (hPb N hPN) hPN
  have hmP : P m := Nat.findGreatest_spec (hPb N hPN) hPN
  have hm : 1 ≤ m := hN.trans hNm
  have hqm : m < q*m := by nlinarith
  have hnP : ¬P (q*m) := by
    intro ht
    exact Nat.findGreatest_is_greatest hqm (hPb (q*m) ht) ht
  have hlarge : N^d*f (q*m) < (q*m)^d := Nat.lt_of_not_ge hnP
  have hbound : m^d ≤ N^d*n := hmP.trans (Nat.mul_le_mul_left _ (hf m).2)
  refine ⟨m,hNm,hbound,?_⟩
  have htrip : N^d*f (q*m) < N^d*(q^d*f m) := by
    calc
      N^d*f (q*m) < (q*m)^d := hlarge
      _ = q^d*m^d := mul_pow _ _ _
      _ ≤ q^d*(N^d*f m) := Nat.mul_le_mul_left _ hmP
      _ = N^d*(q^d*f m) := by ring
  exact (Nat.lt_of_mul_lt_mul_left htrip).le

/-- Convert the natural-power radius bound into a real root bound. -/
theorem polynomial_scale_root_bound {m N n d : ℕ} (hd : 1 ≤ d)
    (h : m^d ≤ N^d*n) : (m : ℝ) ≤ N*(n : ℝ)^(1/(d : ℝ)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hh : (m : ℝ)^d ≤ (N : ℝ)^d*n := by exact_mod_cast h
  have hroot := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (m : ℝ)^d) hh
    (by positivity : (0 : ℝ) ≤ 1/(d : ℝ))
  have hm : ((m : ℝ)^d)^(1/(d : ℝ)) = m := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity),mul_one_div_cancel hdpos.ne',Real.rpow_one]
  have hNN : ((N : ℝ)^d*n)^(1/(d : ℝ)) = N*(n : ℝ)^(1/(d : ℝ)) := by
    rw [Real.mul_rpow (by positivity) (by positivity),← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity),mul_one_div_cancel hdpos.ne',Real.rpow_one]
  simpa only [hm,hNN] using hroot

/-- A polynomial crossing lies at sub-power radius eventually; the
constants are fixed before the growth function is supplied. -/
theorem eventual_small_tripling_scale (lam : ℝ) (hlam : 0 < lam) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ N C : ℕ, 1 ≤ N → 1 ≤ C →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ f : ℕ → ℕ,
        (∀ t, 1 ≤ f t ∧ f t ≤ n) →
        ∃ m : ℕ, N ≤ m ∧ (C*m : ℝ) ≤ (n : ℝ)^lam ∧ f (3*m) ≤ K*f m := by
  obtain ⟨d,hd⟩ := exists_nat_gt (max 1 (1/lam))
  have hd1 : 1 ≤ d := by have := (le_max_left 1 (1/lam)).trans_lt hd; exact_mod_cast this.le
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hexp : 1/(d : ℝ) < lam := by
    apply (div_lt_iff₀ hdpos).mpr
    have hh := (le_max_right 1 (1/lam)).trans_lt hd
    have := (div_lt_iff₀ hlam).mp hh
    nlinarith
  refine ⟨3^d,Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)),?_⟩
  intro N C hN hC
  have hCN : (0 : ℝ) < C*N := by
    have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hC' : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
    positivity
  obtain ⟨n₀,hn₀⟩ := eventually_absorb_constant hexp (show (0 : ℝ) < 1/(C*N) by positivity)
  refine ⟨n₀,?_⟩
  intro n hn f hf
  obtain ⟨m,hm,hpow,htrip⟩ := polynomial_crossing_scale f n N d 3 hf hN hd1 (by omega)
  refine ⟨m,hm,?_,htrip⟩
  have hr := polynomial_scale_root_bound hd1 hpow
  have ha := hn₀ n hn
  have hb : (C*N : ℝ)*(n : ℝ)^(1/(d : ℝ)) ≤ (n : ℝ)^lam := by
    rw [mul_comm (C*N : ℝ)]
    apply (le_div_iff₀ hCN).mp
    convert ha using 1
    ring
  calc
    (C*m : ℝ) ≤ C*(N*(n : ℝ)^(1/(d : ℝ))) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = (C*N : ℝ)*(n : ℝ)^(1/(d : ℝ)) := by ring
    _ ≤ (n : ℝ)^lam := hb

end DirectedCycles
