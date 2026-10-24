import DirectedCycles.NormalClosureCommutators
import DirectedCycles.GroupMultihomOperations

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- Relative central series commute with surjective group homomorphisms. -/
theorem relativeSeries_map {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (N : Subgroup G) (n : ℕ) :
    (relativeSeries N n).map f = relativeSeries (N.map f) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [relativeSeries,Subgroup.map_commutator,Subgroup.map_top_of_surjective f hf,ih]
    rfl

/-- Normal closures of an actual image, and their entire relative series,
are preserved under quotienting. -/
theorem normalClosure_image_relativeSeries {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (S : Set G) (n : ℕ) :
    relativeSeries (Subgroup.normalClosure (f '' S)) n =
      (relativeSeries (Subgroup.normalClosure S) n).map f := by
  rw [relativeSeries_map f hf,Subgroup.map_normalClosure S f hf]

/-- Killing the terminal relative term strictly lowers the height needed
for the normal-envelope induction. -/
theorem relativeSeries_quotient_eq_bot {G : Type*} [Group G]
    (S : Set G) (L : Subgroup G) [L.Normal] (n : ℕ)
    (hL : relativeSeries (Subgroup.normalClosure S) n ≤ L) :
    relativeSeries (Subgroup.normalClosure ((QuotientGroup.mk' L) '' S)) n = ⊥ := by
  rw [normalClosure_image_relativeSeries (QuotientGroup.mk' L) (QuotientGroup.mk'_surjective L)]
  apply (Subgroup.map_eq_bot_iff _).mpr
  rwa [QuotientGroup.ker_mk']

/-- The same height reduction for separately homomorphic images. -/
theorem multihom_relativeSeries_quotient_eq_bot {ι : Type*} [DecidableEq ι]
    {B : ι → Type*} [∀ i, Group (B i)] {G : Type*} [Group G]
    (φ : GroupMultihom B G) (L : Subgroup G) [L.Normal] (n : ℕ)
    (hL : relativeSeries (Subgroup.normalClosure (Set.range φ)) n ≤ L) :
    relativeSeries (Subgroup.normalClosure (Set.range (φ.codComp (QuotientGroup.mk' L)))) n = ⊥ := by
  have he : Set.range (φ.codComp (QuotientGroup.mk' L)) = (QuotientGroup.mk' L) '' Set.range φ := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩; exact ⟨φ x,⟨x,rfl⟩,rfl⟩
    · rintro ⟨g,⟨x,rfl⟩,rfl⟩; exact ⟨x,rfl⟩
  rw [he]
  exact relativeSeries_quotient_eq_bot (Set.range φ) L n hL

end DirectedCycles
