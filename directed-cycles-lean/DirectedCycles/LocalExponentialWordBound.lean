module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {E G : Type*} [NormedAddCommGroup E] [Group G]

/-- A local quantitative product rule controls every bounded-length word,
including all intermediate coordinate values used by the induction. -/
theorem local_exponential_word_bound (exp : E → G) (hzero : exp 0 = 1)
    {q r R : ℝ} (hq : 1 ≤ q) (hr : 0 ≤ r) (hrR : r < R) (M : ℕ)
    (hsize : q^M*(M : ℝ)*r < R)
    (hprod : ∀ x y : E, ‖x‖ < R → ‖y‖ < R →
      ∃ z : E, ‖z‖ ≤ q*(‖x‖+‖y‖) ∧ exp z = exp x*exp y) :
    ∀ l : List G, l.length ≤ M → (∀ x ∈ l, x ∈ exp '' Metric.closedBall 0 r) →
      ∃ z : E, ‖z‖ ≤ q^l.length*(l.length : ℝ)*r ∧ exp z = l.prod := by
  intro l
  induction l with
  | nil =>
    intro _ _
    exact ⟨0,by simp,hzero⟩
  | cons x l ih =>
    intro hlen hmem
    have hlM : l.length ≤ M := by simp only [List.length_cons] at hlen; omega
    obtain ⟨v,hv,he⟩ := hmem x (by simp)
    have hvn : ‖v‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
    obtain ⟨w,hw,hew⟩ := ih hlM (fun y hy => hmem y (by simp only [List.mem_cons]; exact Or.inr hy))
    have hwR : ‖w‖ < R := by
      apply lt_of_le_of_lt hw
      apply lt_of_le_of_lt _ hsize
      gcongr
    obtain ⟨z,hz,hez⟩ := hprod v w (hvn.trans_lt hrR) hwR
    have hpow : 1 ≤ q^l.length := one_le_pow₀ hq
    have hrr : r ≤ q^l.length*r := by nlinarith
    refine ⟨z,?_,?_⟩
    · calc
        ‖z‖ ≤ q*(‖v‖+‖w‖) := hz
        _ ≤ q*(r+q^l.length*(l.length : ℝ)*r) :=
          mul_le_mul_of_nonneg_left (add_le_add hvn hw) (by linarith)
        _ ≤ q*(q^l.length*r+q^l.length*(l.length : ℝ)*r) :=
          mul_le_mul_of_nonneg_left (add_le_add hrr (le_refl _)) (by linarith)
        _ = q^(x::l).length*((x::l).length : ℝ)*r := by
          simp only [List.length_cons,pow_succ,Nat.cast_add,Nat.cast_one]
          ring
    · simpa only [he,hew,List.prod_cons] using hez
end DirectedCycles
