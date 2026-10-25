module

public import DirectedCycles.CompactPowerTrapping
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- Expansion under doubling excludes a nontrivial cyclic subgroup in a
bounded coordinate region. This is the quantitative core of the NSS
argument for differentiable group charts. -/
theorem cyclic_nss_of_doubling_growth (V : Set G) (size : G → ℝ) (c R : ℝ)
    (hc : 1 < c) (hsize : ∀ x ∈ V, 0 ≤ size x)
    (hzero : ∀ x ∈ V, size x = 0 → x = 1)
    (hbound : ∀ x ∈ V, size x ≤ R)
    (hgrowth : ∀ x ∈ V, x*x ∈ V → c*size x ≤ size (x*x)) :
    ∀ x : G, (∀ n : ℕ, x^n ∈ V) → x = 1 := by
  intro x hx
  have hxV : x ∈ V := by simpa only [pow_one] using hx 1
  apply hzero x hxV
  apply le_antisymm _ (hsize x hxV)
  by_contra hn
  have hs : 0 < size x := lt_of_not_ge hn
  have hlower : ∀ n : ℕ, c^n*size x ≤ size (x^(2^n)) := by
    intro n
    induction n with
    | zero => simp only [pow_zero,pow_one,one_mul,le_refl]
    | succ n ih =>
      have hp : x^(2^(n+1)) = x^(2^n)*x^(2^n) := by rw [pow_succ,pow_mul,pow_two]
      rw [hp,pow_succ]
      calc
        c^n*c*size x = c*(c^n*size x) := by ring
        _ ≤ c*size (x^(2^n)) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ size (x^(2^n)*x^(2^n)) := hgrowth _ (hx _) (hp ▸ hx _)
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (R/size x) hc
  have hgt : R < c^n*size x := (div_lt_iff₀ hs).mp hn
  exact (not_lt_of_ge ((hlower n).trans (hbound _ (hx _)))) hgt
end DirectedCycles
