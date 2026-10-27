module

public import DirectedCycles.FiniteGroupDerivatives
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- The discrete Taylor bound is pointwise and does not require a finite
group or the norm on a finite product of function spaces. -/
theorem groupDerivative_taylor_pointwise (f : G → ℝ) (g : G) {n : ℕ} (hn : 0 < n)
    {A B : ℝ} (hpow : ∀ x, |groupDerivative (g^n) f x| ≤ A)
    (hsecond : ∀ i < n, ∀ x, |groupDerivative (g^i) (groupDerivative g f) x| ≤ B) (x : G) :
    |groupDerivative g f x| ≤ A/(n : ℝ)+B := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have he := groupDerivative_pow g f n x
  have he' : (n : ℝ)*groupDerivative g f x = groupDerivative (g^n) f x -
      ∑ i ∈ Finset.range n, groupDerivative (g^i) (groupDerivative g f) x := by linarith
  have hb : |(n : ℝ)*groupDerivative g f x| ≤ A+(n : ℝ)*B := by
    rw [he']
    calc
      _ ≤ |groupDerivative (g^n) f x|+
          |∑ i ∈ Finset.range n, groupDerivative (g^i) (groupDerivative g f) x| := abs_sub _ _
      _ ≤ A+∑ i ∈ Finset.range n, |groupDerivative (g^i) (groupDerivative g f) x| :=
        add_le_add (hpow x) (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ A+∑ _i ∈ Finset.range n, B := add_le_add le_rfl
        (Finset.sum_le_sum (fun i hi => hsecond i (Finset.mem_range.mp hi) x))
      _ = A+(n : ℝ)*B := by simp
  rw [abs_mul,abs_of_pos hnR] at hb
  have heq : (n : ℝ)*(A/(n : ℝ)+B) = A+(n : ℝ)*B := by field_simp
  nlinarith

/-- A uniform generator derivative estimate telescopes over actual
products in a word power. -/
theorem groupDerivative_word_bound {Q : Set G} {f : G → ℝ} {b : ℝ}
    (hb : ∀ q ∈ Q, ∀ x, |groupDerivative q f x| ≤ b) (n : ℕ) :
    ∀ g ∈ Q^n, ∀ x, |groupDerivative g f x| ≤ (n : ℝ)*b := by
  induction n with
  | zero =>
      intro g hg x
      have hg1 : g = 1 := by simpa using hg
      simp [hg1]
  | succ n ih =>
      intro g hg x
      rw [pow_succ'] at hg
      rcases hg with ⟨q,hq,w,hw,rfl⟩
      rw [groupDerivative_mul]
      change |groupDerivative w f (q⁻¹*x)+groupDerivative q f x| ≤ _
      calc
        _ ≤ |groupDerivative w f (q⁻¹*x)|+|groupDerivative q f x| := abs_add_le _ _
        _ ≤ (n : ℝ)*b+b := add_le_add (ih w hw _) (hb q hq x)
        _ = ((n+1 : ℕ) : ℝ)*b := by push_cast; ring

/-- A bump with positive value at one detects escape from its support.
This pointwise version avoids any unproved bounded-function norm facts. -/
theorem groupDerivative_support_detection {f : G → ℝ} {W : Set G} {g : G} {c : ℝ}
    (hc : c ≤ f 1) (hs : ∀ x, x ∉ W → f x = 0)
    (hsmall : ∀ x, |groupDerivative g f x| < c) : g ∈ W := by
  by_contra hg
  have h := hsmall g
  simp only [groupDerivative,leftShift,Pi.sub_apply,inv_mul_cancel,hs g hg,sub_zero] at h
  exact (not_lt_of_ge (hc.trans (le_abs_self _))) h
end DirectedCycles
