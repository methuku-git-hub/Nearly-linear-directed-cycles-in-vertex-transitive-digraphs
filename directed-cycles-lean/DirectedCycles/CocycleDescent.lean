import DirectedCycles.QuotientRepresentation

set_option autoImplicit false
namespace DirectedCycles

/-- The zero set of a crossed homomorphism is an ordinary subgroup. -/
def cocycleZeroSubgroup {G V : Type*} [Group G] [AddCommGroup V]
    {T : G →* Module.End ℤ V} {f : G → V} (hf : IsAdditiveCocycle T f) : Subgroup G where
  carrier := {g | f g = 0}
  one_mem' := cocycle_one hf
  mul_mem' := by intro g h hg hh; change f (g*h) = 0; rw [hf,hg,hh,map_zero,add_zero]
  inv_mem' := by
    intro g hg
    change f g = 0 at hg
    change f g⁻¹ = 0
    have h := hf g⁻¹ g
    simpa only [inv_mul_cancel,cocycle_one hf,hg,map_zero,add_zero] using h.symm

/-- A cocycle constant on kernel cosets descends as a function. -/
def descendedCocycle {G V : Type*} [Group G] [AddCommGroup V]
    {T : G →* Module.End ℤ V} {f : G → V} (hf : IsAdditiveCocycle T f)
    (K : Subgroup G) [K.Normal] (hK : K ≤ cocycleZeroSubgroup hf) : G ⧸ K → V :=
  Quotient.lift f (by
    intro g h hrel
    have hk : f (g⁻¹*h) = 0 := hK (QuotientGroup.leftRel_apply.mp hrel)
    have he := hf g (g⁻¹*h)
    simpa only [mul_inv_cancel_left,hk,map_zero,add_zero] using he.symm)

@[simp] theorem descendedCocycle_mk {G V : Type*} [Group G] [AddCommGroup V]
    {T : G →* Module.End ℤ V} {f : G → V} (hf : IsAdditiveCocycle T f)
    (K : Subgroup G) [K.Normal] (hK : K ≤ cocycleZeroSubgroup hf) (g : G) :
    descendedCocycle hf K hK (QuotientGroup.mk' K g) = f g := rfl

/-- If the representation also descends, the quotient function remains a cocycle. -/
theorem descendedCocycle_identity {G V : Type*} [Group G] [AddCommGroup V]
    {T : G →* Module.End ℤ V} {f : G → V} (hf : IsAdditiveCocycle T f)
    (K : Subgroup G) [K.Normal] (hK : K ≤ cocycleZeroSubgroup hf) (hT : K ≤ T.ker) :
    IsAdditiveCocycle (QuotientGroup.lift K T hT) (descendedCocycle hf K hK) := by
  intro x y
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective K x
  obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective K y
  exact hf g h

/-- Applying an equivariant quotient map preserves the cocycle equation. -/
theorem quotientCocycle_identity {G V : Type*} [Group G] [AddCommGroup V]
    {T : G →* Module.End ℤ V} {f : G → V} (hf : IsAdditiveCocycle T f)
    (W : Submodule ℤ V) (hW : ∀ g : G, W ≤ W.comap (T g)) :
    IsAdditiveCocycle (quotientRepresentation T W hW) (fun g => W.mkQ (f g)) := by
  intro g h
  change W.mkQ (f (g*h)) = W.mkQ (f g) + quotientRepresentation T W hW g (W.mkQ (f h))
  rw [hf,map_add,quotientRepresentation_mk]

end DirectedCycles
