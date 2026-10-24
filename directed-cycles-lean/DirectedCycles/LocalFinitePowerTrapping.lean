import DirectedCycles.LocalNormGrowthNSS
import DirectedCycles.LocalPowerSegment

set_option autoImplicit false
namespace DirectedCycles.LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A bounded finite segment of genuine local powers must start arbitrarily
close to zero in an expanding size function once the segment is long enough. -/
theorem finite_power_trapping_of_doubling_growth (V : Set G) (size : G → ℝ) (c R : ℝ)
    (hc : 1 < c) (hbound : ∀ x ∈ V, size x ≤ R)
    (hgrowth : ∀ x ∈ V, ∀ y ∈ V, L.mulRel x x y → c*size x ≤ size y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ x : G, (∀ n ≤ M, L.PowerIn V x n) → size x < ε := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (R/ε) hc
  have hgt : R < c^k*ε := (div_lt_iff₀ hε).mp hk
  have hN : 1 ≤ 2^k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  refine ⟨2^k,hN,?_⟩
  intro x hx
  let p := L.powerSegmentOfPowerIn hx
  have hp : ∀ n ≤ 2^k, p.power n ∈ V := fun n hn => L.powerSegmentOfPowerIn_mem hx hn
  have hlower : ∀ n ≤ k, c^n*size x ≤ size (p.power (2^n)) := by
    intro n hn
    induction n with
    | zero => simp only [pow_zero,p.one hN,_root_.one_mul,le_refl]
    | succ n ih =>
      have he : 2^(n+1) = 2^n+2^n := by omega
      have hb : 2^(n+1) ≤ 2^k := Nat.pow_le_pow_right (by omega) hn
      have hn' : 2^n ≤ 2^k := Nat.pow_le_pow_right (by omega) (by omega)
      rw [he,pow_succ]
      calc
        c^n*c*size x = c*(c^n*size x) := by ring
        _ ≤ c*size (p.power (2^n)) := mul_le_mul_of_nonneg_left (ih (by omega)) (by linarith)
        _ ≤ size (p.power (2^n+2^n)) :=
          hgrowth _ (hp _ hn') _ (hp _ (he ▸ hb)) (p.add (he ▸ hb))
  by_contra hn
  have hlow : c^k*ε ≤ c^k*size x := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (by positivity)
  exact (not_lt_of_ge (hlow.trans ((hlower k le_rfl).trans (hbound _ (hp _ le_rfl))))) hgt
end DirectedCycles.LocalGroupAlgebra
