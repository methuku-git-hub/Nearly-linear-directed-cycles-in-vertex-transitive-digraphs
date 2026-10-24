import DirectedCycles.LocalTranslationComposition
import DirectedCycles.LocalPowerSegment

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem derivative_one (hL : L.Cancellative) (f : G → ℝ) : L.derivative L.one f = 0 := by
  unfold derivative
  rw [L.leftShift_one hL,sub_self]

/-- Exact discrete Taylor identity for a genuinely defined finite power
segment. Only its stated finite range is used. -/
theorem derivative_powerSegment (hL : L.Cancellative) {A : Set G}
    (hdom : L.AllProductsDefined A 3) {g : G} {N : ℕ}
    (p : L.PowerSegment g N) (hp : ∀ i ≤ N, p.power i ∈ A) (hg : g ∈ A)
    (f : G → ℝ) (hf : ∀ x, f x ≠ 0 → x ∈ A) {n : ℕ} (hn : n ≤ N) (x : G) :
    L.derivative (p.power n) f x = (n : ℝ)*L.derivative g f x +
      ∑ i ∈ Finset.range n, L.derivative (p.power i) (L.derivative g f) x := by
  induction n with
  | zero => simp only [p.zero,L.derivative_one hL,Pi.zero_apply,Nat.cast_zero,
      zero_mul,Finset.sum_range_zero,add_zero]
  | succ n ih =>
    have hmul : L.mulRel (p.power n) g (p.power (n+1)) := by
      simpa only [p.one (by omega : 1 ≤ N)] using p.add hn
    rw [L.derivative_mul hL hdom (hp n (by omega)) hg hmul f hf,
      Pi.add_apply,ih (by omega),Finset.sum_range_succ]
    simp only [Nat.cast_add,Nat.cast_one,derivative,Pi.sub_apply]
    ring

section Finite
variable [Fintype G]

theorem derivativeNorm_nonneg (f : G → ℝ) (g : G) : 0 ≤ L.derivativeNorm f g := norm_nonneg _

theorem derivativeNorm_le_iff (f : G → ℝ) (g : G) {r : ℝ} (hr : 0 ≤ r) :
    L.derivativeNorm f g ≤ r ↔ ∀ x, |L.derivative g f x| ≤ r :=
  pi_norm_le_iff_of_nonneg hr

/-- The local Taylor estimate has the same numerical bound as the global
one, with all domain and finite-power requirements explicit and proved. -/
theorem derivativeNorm_taylor_bound (hL : L.Cancellative) {A : Set G}
    (hdom : L.AllProductsDefined A 3) {g : G} {N : ℕ}
    (p : L.PowerSegment g N) (hp : ∀ i ≤ N, p.power i ∈ A) (hg : g ∈ A)
    (f : G → ℝ) (hf : ∀ x, f x ≠ 0 → x ∈ A) {n : ℕ} (hn : n ≤ N) (hnpos : 0 < n) :
    L.derivativeNorm f g ≤ (2*‖f‖ +
      ∑ i ∈ Finset.range n, L.derivativeNorm (L.derivative g f) (p.power i)) / n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hnum : 0 ≤ 2*‖f‖ + ∑ i ∈ Finset.range n,
      L.derivativeNorm (L.derivative g f) (p.power i) :=
    add_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
      (Finset.sum_nonneg fun i _ => L.derivativeNorm_nonneg _ _)
  apply (L.derivativeNorm_le_iff f g (div_nonneg hnum hnR.le)).2
  intro x
  rw [le_div_iff₀ hnR]
  have he := L.derivative_powerSegment hL hdom p hp hg f hf hn x
  have he' : (n : ℝ)*L.derivative g f x = L.derivative (p.power n) f x -
      ∑ i ∈ Finset.range n, L.derivative (p.power i) (L.derivative g f) x := by linarith
  calc
    |L.derivative g f x| * (n : ℝ) = |(n : ℝ)*L.derivative g f x| := by
      rw [abs_mul,abs_of_pos hnR,mul_comm]
    _ ≤ |L.derivative (p.power n) f x| +
        |∑ i ∈ Finset.range n, L.derivative (p.power i) (L.derivative g f) x| := by
      rw [he']
      exact abs_sub _ _
    _ ≤ L.derivativeNorm f (p.power n) +
        ∑ i ∈ Finset.range n, L.derivativeNorm (L.derivative g f) (p.power i) :=
      add_le_add (L.abs_derivative_le _ _ _)
        ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => L.abs_derivative_le _ _ _))
    _ ≤ 2*‖f‖ + ∑ i ∈ Finset.range n, L.derivativeNorm (L.derivative g f) (p.power i) :=
      add_le_add (L.derivativeNorm_le_two_mul f (p.power n)) le_rfl
end Finite
end LocalGroupAlgebra
end DirectedCycles
