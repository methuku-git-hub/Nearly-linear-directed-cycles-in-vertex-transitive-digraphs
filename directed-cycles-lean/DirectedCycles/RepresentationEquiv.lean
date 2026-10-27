module

public import DirectedCycles.QuotientRepresentation
public import DirectedCycles.UnipotentRecurrence

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Every group representation by endomorphisms consists of automorphisms. -/
def representationEquiv {G V : Type*} [Group G] [AddCommGroup V]
    (T : G →* Module.End ℤ V) (g : G) : V ≃ₗ[ℤ] V where
  toLinearMap := T g
  invFun := T g⁻¹
  left_inv v := by
    change (T g⁻¹*T g) v = v
    rw [← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  right_inv v := by
    change (T g*T g⁻¹) v = v
    rw [← map_mul,mul_inv_cancel,map_one,Module.End.one_apply]

@[simp] theorem representationEquiv_apply {G V : Type*} [Group G] [AddCommGroup V]
    (T : G →* Module.End ℤ V) (g : G) (v : V) : representationEquiv T g v = T g v := rfl

/-- The automorphisms retain the original group multiplication. -/
def representationEquivHom {G V : Type*} [Group G] [AddCommGroup V]
    (T : G →* Module.End ℤ V) : G →* (V ≃ₗ[ℤ] V) where
  toFun := representationEquiv T
  map_one' := by apply LinearEquiv.ext; intro v; change T 1 v = v; rw [map_one,Module.End.one_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change T (g*h) v = T g (T h v)
    rw [map_mul,Module.End.mul_apply]

theorem representationEquiv_zpow {G V : Type*} [Group G] [AddCommGroup V]
    (T : G →* Module.End ℤ V) (g : G) (k : ℤ) (v : V) :
    T (g^k) v = ((representationEquiv T g)^k) v := by
  have h := congrArg (fun e : V ≃ₗ[ℤ] V => e v) (map_zpow (representationEquivHom T) g k)
  exact h

end DirectedCycles
