module

public import DirectedCycles.Thresholds

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A uniform natural cutoff absorbs a fixed positive loss by any positive
power of an order above the cutoff. -/
theorem exists_prime_loss_cutoff (alpha eta : ℝ) (ha : 0 < alpha) (he : 0 < eta) :
    ∃ P : ℕ, ∀ K : ℝ, (P : ℝ) < K → K^(-eta) ≤ alpha := by
  obtain ⟨P,hP⟩ := exists_nat_gt ((1/alpha)^(1/eta))
  refine ⟨P,?_⟩
  intro K hK
  have hx : 0 < (1/alpha)^(1/eta) := Real.rpow_pos_of_pos (by positivity) _
  have hKpos : 0 < K := hx.trans (hP.trans hK)
  have hpow : 1/alpha ≤ K^eta := by
    calc
      1/alpha = ((1/alpha)^(1/eta))^eta := by
        rw [← Real.rpow_mul (by positivity),one_div_mul_cancel he.ne',Real.rpow_one]
      _ ≤ K^eta := Real.rpow_le_rpow hx.le (hP.trans hK).le he.le
  rw [Real.rpow_neg hKpos.le]
  exact (inv_le_comm₀ (Real.rpow_pos_of_pos hKpos eta) ha).mpr (by simpa only [one_div] using hpow)

/-- One large-prime reconstruction step. A small selected prime consumes a
budget unit; otherwise the order of K absorbs the extra constant. -/
theorem prime_loss_recurrence (alpha eta q K B ell L : ℝ) (bg bq : ℕ)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (he : 0 ≤ eta)
    (hq : 0 < q) (hK : 1 ≤ K) (hB : 0 < B) (hBK : B ≤ K)
    (hbudget : bq ≤ bg) (hcharge : bq+1 ≤ bg ∨ K^(-eta) ≤ alpha)
    (hell : alpha^bq*q^(1-2*eta) ≤ ell)
    (hL : alpha*ell*K*B^(-eta) ≤ L) :
    alpha^bg*(q*K)^(1-2*eta) ≤ L := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hkp : 0 ≤ K^(-eta) := Real.rpow_nonneg hKpos.le _
  have hbp : 0 ≤ B^(-eta) := Real.rpow_nonneg hB.le _
  have hpay : alpha^bg*K^(-eta) ≤ alpha*alpha^bq := by
    rcases hcharge with hd | hl
    · have hh := pow_le_pow_of_le_one ha.le ha1 hd
      rw [pow_succ] at hh
      have hk1 := Real.rpow_le_one_of_one_le_of_nonpos hK (by linarith : -eta ≤ 0)
      calc
        alpha^bg*K^(-eta) ≤ alpha^bg := mul_le_of_le_one_right (pow_nonneg ha.le _) hk1
        _ ≤ alpha*alpha^bq := by simpa only [mul_comm] using hh
    · have hh := pow_le_pow_of_le_one ha.le ha1 hbudget
      calc
        alpha^bg*K^(-eta) ≤ alpha^bq*alpha :=
          mul_le_mul hh hl hkp (pow_nonneg ha.le _)
        _ = alpha*alpha^bq := mul_comm _ _
  have hbpge : K^(-eta) ≤ B^(-eta) :=
    Real.rpow_le_rpow_of_nonpos hB hBK (by linarith)
  have hdouble := mul_le_mul hpay hbpge hkp (mul_nonneg ha.le (pow_nonneg ha.le bq))
  have hidentity : alpha^bg*(q*K)^(1-2*eta) =
      (alpha^bg*K^(-eta)*K^(-eta))*(q^(1-2*eta)*K) := by
    rw [Real.mul_rpow hq.le hKpos.le]
    have ht : K^(1-2*eta) = K*(K^(-eta)*K^(-eta)) := by
      calc
        K^(1-2*eta) = K^(1+(-eta+-eta)) := by congr 1; ring
        _ = K*(K^(-eta)*K^(-eta)) := by rw [Real.rpow_add hKpos,Real.rpow_one,Real.rpow_add hKpos]
    rw [ht]
    ring
  rw [hidentity]
  calc
    (alpha^bg*K^(-eta)*K^(-eta))*(q^(1-2*eta)*K) ≤
        (alpha*alpha^bq*B^(-eta))*(q^(1-2*eta)*K) :=
      mul_le_mul_of_nonneg_right hdouble (mul_nonneg (Real.rpow_nonneg hq.le _) hKpos.le)
    _ = alpha*(alpha^bq*q^(1-2*eta))*K*B^(-eta) := by ring
    _ ≤ alpha*ell*K*B^(-eta) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hell ha.le) hKpos.le) hbp
    _ ≤ L := hL

end DirectedCycles
