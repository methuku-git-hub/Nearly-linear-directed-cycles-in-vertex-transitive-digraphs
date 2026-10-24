import DirectedCycles.FiniteNSSProgressionRestoration

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Bounded powers in the quotient fourth power lift to the fifth power
upstairs. Thus the actual strong trapping test descends to the quotient. -/
theorem quotient_fourth_power_trapping {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) (A : Set G) (hA1 : 1 ∈ A)
    (hker : (q.ker : Set G) ⊆ A)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 → x^j ∈ A^100) → x ∈ A) :
    ∀ y : Q, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 → y^j ∈ (q '' A)^4) → y ∈ q '' A := by
  intro y hy
  obtain ⟨x,rfl⟩ := hq y
  refine ⟨x,htrap x ?_,rfl⟩
  intro j hj hjmax
  have hh := hy j hj hjmax
  rw [← Set.image_pow] at hh
  obtain ⟨b,hb,hbq⟩ := hh
  have hk : x^j*b⁻¹ ∈ q.ker := by
    change q (x^j*b⁻¹) = 1
    rw [map_mul,map_pow,map_inv,hbq,mul_inv_cancel]
  have hfive : x^j ∈ A^5 := by
    change x^j ∈ A^(1+4)
    rw [pow_add,pow_one]
    exact ⟨x^j*b⁻¹,hker hk,b,hb,inv_mul_cancel_right _ _⟩
  exact Set.pow_subset_pow_right hA1 (by omega : 5 ≤ 100) hfive

/-- The quotient fourth power is NSS when its power test traps back into
an NSS first power. This supplies the exact enlarged source window used by
the initial good model. -/
theorem quotient_fourth_power_cyclic_nss {Q : Type*} [Group Q] (B : Set Q)
    (htrap : ∀ y : Q, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 → y^j ∈ B^4) → y ∈ B)
    (hNSS : ∀ y : Q, (∀ n : ℕ, y^n ∈ B) → y = 1) :
    ∀ y : Q, (∀ n : ℕ, y^n ∈ B^4) → y = 1 := by
  intro y hy
  apply hNSS y
  intro n
  apply htrap (y^n)
  intro j _hj _hjmax
  simpa only [← pow_mul] using hy (n*j)
end DirectedCycles
