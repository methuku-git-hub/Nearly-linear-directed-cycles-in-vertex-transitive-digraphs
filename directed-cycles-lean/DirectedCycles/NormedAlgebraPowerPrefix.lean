import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace DirectedCycles
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- If every initial power stays close to one, the power expansion has
a uniform first-order remainder bound. No spectral assumption is used. -/
theorem normedAlgebra_power_prefix_error (a : A) (R : ℝ) (_hR : 0 ≤ R) (N : ℕ)
    (hp : ∀ k ≤ N, ‖a^k-1‖ ≤ R) :
    ‖a^N-1-(N : ℝ) • (a-1)‖ ≤ (N : ℝ)*R*‖a-1‖ := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun k hk => hp k (by omega))
    have heq : a^(n+1)-1-((n+1 : ℕ) : ℝ) • (a-1) =
        (a^n-1-(n : ℝ) • (a-1))+(a^n-1)*(a-1) := by
      rw [Nat.cast_add,Nat.cast_one,add_smul,one_smul,pow_succ]
      noncomm_ring
    rw [heq]
    have hm := (norm_mul_le (a^n-1) (a-1)).trans
      (mul_le_mul_of_nonneg_right (hp n (by omega)) (norm_nonneg (a-1)))
    have ht := (norm_add_le _ _).trans (add_le_add hi hm)
    exact ht.trans_eq (by push_cast; ring)

/-- A small power prefix forces its generator to have size inversely
proportional to the prefix length. -/
theorem normedAlgebra_power_prefix_bound (a : A) (R : ℝ) (hR : 0 ≤ R) (hRsmall : R ≤ 1/2)
    (N : ℕ) (hp : ∀ k ≤ N, ‖a^k-1‖ ≤ R) : (N : ℝ)*‖a-1‖ ≤ 2*R := by
  have he := normedAlgebra_power_prefix_error a R hR N hp
  have ht := norm_sub_le (a^N-1) (a^N-1-(N : ℝ) • (a-1))
  rw [sub_sub_cancel] at ht
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg N)] at ht
  have hb := ht.trans (add_le_add (hp N le_rfl) he)
  have hn : 0 ≤ (N : ℝ)*‖a-1‖ := mul_nonneg (Nat.cast_nonneg N) (norm_nonneg _)
  have hr := mul_le_mul_of_nonneg_right hRsmall hn
  nlinarith

end DirectedCycles
