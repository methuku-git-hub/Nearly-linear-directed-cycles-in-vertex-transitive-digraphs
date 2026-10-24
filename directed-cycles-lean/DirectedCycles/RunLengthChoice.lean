import DirectedCycles.RunLengthAllocation

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- The run lengths in Theorem 5.1 exist with the source bounds, closure
congruence, and strict quarter-density lower bound. -/
theorem choose_run_lengths (ell h D : ℕ) (hell : 2 ≤ ell) (hh : 8*D+4 < h) (nu : ℤ) :
    ∃ l : Fin ell → ℕ,
      (∀ i, D ≤ l i ∧ l i ≤ h-2*D-2) ∧
      (h : ℤ) ∣ ((∑ i, (l i+D)) : ℤ)+nu ∧
      (ell : ℝ)*h/4 < ((∑ i, (l i+1 : ℕ)) : ℝ) := by
  let upper := h-2*D-2
  let cap := upper-D
  have hu : upper+2*D+2 = h := by dsimp [upper]; omega
  have hcap : cap+D = upper := by dsimp [cap]; omega
  have hpos : (0 : ℤ) < h := by omega
  let z : ℤ := ((ell*(upper+D) : ℕ) : ℤ)+nu
  let t : ℕ := (z % (h : ℤ)).toNat
  have htcast : (t : ℤ) = z % h := Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))
  have ht : t < h := by
    have hm := Int.emod_lt_of_pos z hpos
    rw [← htcast] at hm
    exact_mod_cast hm
  obtain ⟨d,hd,hs⟩ := two_position_allocation ell cap t hell (by omega)
  let l : Fin ell → ℕ := fun i => upper-d i
  have hdU : ∀ i, d i ≤ upper := fun i => (hd i).trans (by omega)
  have hbounds : ∀ i, D ≤ l i ∧ l i ≤ upper := by
    intro i
    have hdi := hd i
    dsimp [l]
    omega
  have hsum : (∑ i, l i)+t = ell*upper := by
    rw [← hs,← Finset.sum_add_distrib]
    calc (∑ i, (l i+d i)) = ∑ _i : Fin ell, upper := by
           apply Finset.sum_congr rfl
           intro i _
           exact Nat.sub_add_cancel (hdU i)
         _ = _ := by simp
  refine ⟨l,hbounds,?_,?_⟩
  · have he : ((∑ i, (l i+D)) : ℤ)+nu = z-(t : ℤ) := by
      have hsum' : ((∑ i, l i) : ℤ)+t = (ell : ℤ)*upper := by exact_mod_cast hsum
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul] at *
      dsimp only [z]
      push_cast
      nlinarith
    rw [he,htcast]
    refine ⟨z/(h : ℤ),?_⟩
    have hdv := Int.emod_add_mul_ediv z (h : ℤ)
    omega
  · have hT : (∑ i : Fin ell, (l i+1 : ℕ))+t = ell*(upper+1) := by
      have hsone : (∑ _i : Fin ell, (1 : ℕ)) = ell := by simp
      rw [Finset.sum_add_distrib,hsone,Nat.mul_add,Nat.mul_one]
      omega
    simpa only [Nat.cast_sum] using run_length_total_bound ell h D upper _ t hell hh hu ht hT

end DirectedCycles
