import DirectedCycles.AbelianExponent
import DirectedCycles.CyclicLayerRounds

set_option autoImplicit false
namespace DirectedCycles

/-- A generating set of bounded-order elements in a finite abelian group
bounds its order in terms of the generator rank. -/
theorem abelian_card_of_bounded_generator_orders {G : Type*} [CommGroup G] [Finite G]
    (S : Set G) (hS : Subgroup.closure S = ⊤) (P r : ℕ) (hr : Group.rank G ≤ r)
    (hord : ∀ x ∈ S, orderOf x ≤ P) : Nat.card G ≤ P.factorial^r := by
  let : Fintype G := Fintype.ofFinite G
  let H : Subgroup G := {
    carrier := {x | x^P.factorial = 1}
    one_mem' := one_pow _
    mul_mem' := by
      intro x y hx hy
      change x^P.factorial = 1 at hx
      change y^P.factorial = 1 at hy
      change (x*y)^P.factorial = 1
      rw [mul_pow,hx,hy,mul_one]
    inv_mem' := by
      intro x hx
      change x^P.factorial = 1 at hx
      change (x⁻¹)^P.factorial = 1
      rw [inv_pow,hx,inv_one] }
  have hSH : Subgroup.closure S ≤ H := by
    apply H.closure_le.mpr
    intro x hx
    apply orderOf_dvd_iff_pow_eq_one.mp
    exact Nat.dvd_factorial (isOfFinOrder_of_finite x).orderOf_pos (hord x hx)
  have hall : ∀ x : G, x^P.factorial = 1 := fun x => hSH (hS ▸ Subgroup.mem_top x)
  have h := finite_abelian_card_le_exponent_rank P.factorial (Nat.factorial_pos _) hall
  rw [Nat.card_eq_fintype_card]
  exact h.trans (Nat.pow_le_pow_right (Nat.factorial_pos _) hr)

/-- The bounded-round case in the abelian layer argument. -/
theorem abelian_card_of_bounded_round_orders {G : Type*} [CommGroup G] [Finite G]
    {T : ℕ} (S : ZMod T → Set G) (hsc : StronglyConnected (CyclicLayerDigraph S))
    (P r : ℕ) (hr : Group.rank G ≤ r)
    (hord : ∀ x ∈ layerRoundProducts S, orderOf x ≤ P) : Nat.card G ≤ P.factorial^r :=
  abelian_card_of_bounded_generator_orders (layerRoundProducts S)
    (cyclicLayer_rounds_generate S hsc) P r hr hord

end DirectedCycles
