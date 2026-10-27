module

public import DirectedCycles.NilpotentOrder
public import DirectedCycles.ElementNormalClosure
public import DirectedCycles.CyclicLayerRounds

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Bounded orders of a generating set bound the exponent of the
abelianization, and hence the order of a bounded-rank nilpotent group. -/
theorem nilpotent_card_of_bounded_generator_orders {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] (S : Set G) (hS : Subgroup.closure S = ⊤)
    (r c P : ℕ) (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c)
    (hord : ∀ x ∈ S, orderOf x ≤ P) :
    Nat.card G ≤ P.factorial^(∑ i ∈ Finset.range c,r^(i+1)) := by
  let E : Subgroup (Abelianization G) := {
    carrier := {x | x^P.factorial = 1}
    one_mem' := one_pow _
    mul_mem' := by
      intro x y hx hy
      change x^P.factorial=1 at hx
      change y^P.factorial=1 at hy
      change (x*y)^P.factorial=1
      rw [mul_pow,hx,hy,mul_one]
    inv_mem' := by
      intro x hx
      change x^P.factorial=1 at hx
      change (x⁻¹)^P.factorial=1
      rw [inv_pow,hx,inv_one] }
  have hgen : Subgroup.closure (Abelianization.of '' S) = ⊤ := by
    rw [← MonoidHom.map_closure,hS]
    apply Subgroup.map_top_of_surjective
    exact QuotientGroup.mk_surjective
  have hle : Subgroup.closure (Abelianization.of '' S) ≤ E := by
    apply E.closure_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    change (Abelianization.of x)^P.factorial=1
    rw [← map_pow]
    have hxpow : x^P.factorial=1 := orderOf_dvd_iff_pow_eq_one.mp
      (Nat.dvd_factorial (isOfFinOrder_of_finite x).orderOf_pos (hord x hx))
    rw [hxpow,map_one]
  apply nilpotent_order_bound r c P.factorial hr hc (Nat.factorial_pos _)
  intro x
  exact hle (hgen ▸ Subgroup.mem_top x)

/-- Bounded cyclic normal factors of all full-round products bound the
whole group order, uniformly in the number of layers. -/
theorem nilpotent_card_of_bounded_round_factors {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] {T : ℕ} (S : ZMod T → Set G)
    (hsc : StronglyConnected (CyclicLayerDigraph S)) (r c P : ℕ)
    (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c)
    (hf : ∀ x ∈ layerRoundProducts S,
      Nat.card (elementClosure x ⧸ (elementCommutators x).subgroupOf (elementClosure x)) ≤ P) :
    Nat.card G ≤ (P^(c*∑ i ∈ Finset.range c,r^(i+1))).factorial^
      (∑ i ∈ Finset.range c,r^(i+1)) := by
  apply nilpotent_card_of_bounded_generator_orders (layerRoundProducts S)
    (cyclicLayer_rounds_generate S hsc) r c _ hr hc
  intro x hx
  have horder : orderOf x ≤ Nat.card (elementClosure x) := Nat.le_of_dvd Nat.card_pos
    ((elementClosure x).orderOf_dvd_natCard (mem_elementClosure x))
  exact horder.trans ((elementClosure_order_bound x r c hr hc).trans
    (Nat.pow_le_pow_left (hf x hx) _))

end DirectedCycles
