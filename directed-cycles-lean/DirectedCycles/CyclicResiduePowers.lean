module

public import DirectedCycles.PowerCosetCoordinates
public import Mathlib.Data.ZMod.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

noncomputable def residuePower {G : Type*} [Group G] (a : G) (z : ZMod (orderOf a)) : G := a^z.val

theorem residuePower_zero {G : Type*} [Group G] (a : G) : residuePower a 0 = 1 := by
  simp [residuePower]

theorem residuePower_natCast {G : Type*} [Group G] (a : G) (n : ℕ) :
    residuePower a (n : ZMod (orderOf a)) = a^n := by
  simp only [residuePower,ZMod.val_natCast,pow_mod_orderOf]

theorem residuePower_add {G : Type*} [Group G] (a : G) [NeZero (orderOf a)]
    (x y : ZMod (orderOf a)) : residuePower a (x+y) = residuePower a x*residuePower a y := by
  simp only [residuePower,ZMod.val_add,pow_mod_orderOf,pow_add]

theorem residuePower_neg {G : Type*} [Group G] (a : G) [NeZero (orderOf a)]
    (x : ZMod (orderOf a)) : residuePower a (-x) = (residuePower a x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← residuePower_add,neg_add_cancel,residuePower_zero]

theorem residuePower_injective {G : Type*} [Group G] (a : G) [NeZero (orderOf a)] :
    Function.Injective (residuePower a) := by
  intro x y hxy
  exact ZMod.val_injective _ (pow_injOn_Iio_orderOf (ZMod.val_lt x) (ZMod.val_lt y) hxy)

theorem residuePower_intCast {G : Type*} [Group G] (a : G) [NeZero (orderOf a)] (z : ℤ) :
    residuePower a (z : ZMod (orderOf a)) = a^z := by
  cases z with
  | ofNat n =>
    change residuePower a ((n : ℤ) : ZMod (orderOf a)) = a^(n : ℤ)
    rw [Int.cast_natCast,zpow_natCast,residuePower_natCast]
  | negSucc n =>
    have hz : Int.negSucc n = -((n+1 : ℕ) : ℤ) := by simp only [Int.negSucc_eq,Nat.cast_add,Nat.cast_one]
    rw [hz,Int.cast_neg,Int.cast_natCast,residuePower_neg,residuePower_natCast,zpow_neg,zpow_natCast]

theorem residuePower_central {G : Type*} [Group G] (a : G) (ha : a ∈ Subgroup.center G)
    (z : ZMod (orderOf a)) (g : G) : Commute (residuePower a z) g := by
  have hc : Commute a g := (Subgroup.mem_center_iff.mp ha g).symm
  exact hc.pow_left z.val

end DirectedCycles
