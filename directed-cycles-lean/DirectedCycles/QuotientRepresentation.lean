module

public import DirectedCycles.CocycleDifferences
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- An invariant submodule gives an actual quotient representation. -/
def quotientRepresentation {G V : Type*} [Group G] [AddCommGroup V]
    (T : G →* Module.End ℤ V) (W : Submodule ℤ V)
    (hW : ∀ g : G, W ≤ W.comap (T g)) : G →* Module.End ℤ (V ⧸ W) where
  toFun g := W.mapQ W (T g) (hW g)
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨v,rfl⟩ := W.mkQ_surjective x
    change W.mkQ (T 1 v) = W.mkQ v
    rw [map_one,Module.End.one_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    obtain ⟨v,rfl⟩ := W.mkQ_surjective x
    change W.mkQ (T (g*h) v) = W.mkQ (T g (T h v))
    rw [map_mul,Module.End.mul_apply]

@[simp] theorem quotientRepresentation_mk {G V : Type*} [Group G] [AddCommGroup V]
    (T : G →* Module.End ℤ V) (W : Submodule ℤ V)
    (hW : ∀ g : G, W ≤ W.comap (T g)) (g : G) (v : V) :
    quotientRepresentation T W hW g (W.mkQ v) = W.mkQ (T g v) := rfl

/-- Ordered differences commute with the quotient map. -/
theorem quotientRepresentation_difference_product {G V : Type*} [Group G] [AddCommGroup V]
    (T : G →* Module.End ℤ V) (W : Submodule ℤ V)
    (hW : ∀ g : G, W ≤ W.comap (T g)) (gs : List G) (v : V) :
    (gs.map (fun g => quotientRepresentation T W hW g-1)).prod (W.mkQ v) =
      W.mkQ ((gs.map (fun g => T g-1)).prod v) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change (quotientRepresentation T W hW g-1)
      ((gs.map (fun g => quotientRepresentation T W hW g-1)).prod (W.mkQ v)) = _
    rw [ih]
    change W.mkQ (T g _) - W.mkQ _ = W.mkQ (T g _ - _)
    rw [map_sub]
    rfl

/-- A commuting operator preserves the image of a difference. -/
theorem representation_difference_range_invariant {G V : Type*} [Group G] [AddCommGroup V]
    (T : G →* Module.End ℤ V) (a : G)
    (ha : ∀ g : G, Commute (T g) (T a)) :
    ∀ g : G, LinearMap.range (1-T a) ≤ (LinearMap.range (1-T a)).comap (T g) := by
  intro g x hx
  obtain ⟨v,rfl⟩ := hx
  refine ⟨T g v,?_⟩
  change T g v-T a (T g v) = T g (v-T a v)
  rw [map_sub]
  exact congrArg (fun f : Module.End ℤ V => T g v-f v) (ha g).eq.symm

/-- Quotienting by I-T(a) kills the action of a. -/
theorem quotientRepresentation_at_difference {G V : Type*} [Group G] [AddCommGroup V]
    (T : G →* Module.End ℤ V) (a : G)
    (ha : ∀ g : G, Commute (T g) (T a)) :
    quotientRepresentation T (LinearMap.range (1-T a))
      (representation_difference_range_invariant T a ha) a = 1 := by
  let W := LinearMap.range (1-T a)
  apply LinearMap.ext
  intro x
  obtain ⟨v,rfl⟩ := W.mkQ_surjective x
  change W.mkQ (T a v) = W.mkQ v
  apply (sub_eq_zero.mp)
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero W).mpr
  refine ⟨-v,?_⟩
  change -v-T a (-v) = T a v-v
  rw [map_neg]
  abel

end DirectedCycles
