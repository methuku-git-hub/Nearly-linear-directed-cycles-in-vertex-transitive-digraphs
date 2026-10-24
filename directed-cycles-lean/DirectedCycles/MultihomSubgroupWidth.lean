import DirectedCycles.FiniteMultihomWidth
import DirectedCycles.MultihomAbelianization

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles.GroupMultihom

/-- For an abelian target, separate homomorphisms factor through the
abelianization of every source. Thus the finite width result in fact holds
without requiring the source groups to be nilpotent. -/
theorem finite_range_width {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {B : ι → Type*} [∀ i, Group (B i)] [∀ i, Finite (B i)]
    {G : Type*} [CommGroup G] [Finite G] (φ : GroupMultihom B G) :
    (Subgroup.closure (Set.range φ) : Set G) ⊆ (Set.range φ)^(Group.rank G) := by
  let : ∀ i, Finite (Abelianization (B i)) := fun i =>
    Finite.of_surjective (Abelianization.of : B i → Abelianization (B i))
      (QuotientGroup.mk'_surjective (commutator (B i)))
  have h := φ.abelianizationDom.finite_nilpotent_range_width
  simpa only [abelianizationDom_range] using h

def codRestrict {ι : Type*} [DecidableEq ι]
    {B : ι → Type*} [∀ i, Group (B i)] {G : Type*} [Group G]
    (φ : GroupMultihom B G) (H : Subgroup G) (hH : Set.range φ ⊆ H) :
    GroupMultihom B H where
  toFun x := ⟨φ x,hH ⟨x,rfl⟩⟩
  map_one x i := Subtype.ext (φ.map_one x i)
  map_mul x i a b := Subtype.ext (φ.map_mul x i a b)

/-- The rank bound may be taken in any abelian subgroup containing the image. -/
theorem finite_range_width_in_subgroup {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {B : ι → Type*} [∀ i, Group (B i)] [∀ i, Finite (B i)]
    {G : Type*} [CommGroup G] [Finite G] (φ : GroupMultihom B G)
    (H : Subgroup G) (hH : Set.range φ ⊆ H) (r : ℕ) (hr : Group.rank H ≤ r) :
    (Subgroup.closure (Set.range φ) : Set G) ⊆ (Set.range φ)^r := by
  let ψ := φ.codRestrict H hH
  have hrange : H.subtype '' Set.range ψ = Set.range φ := by
    ext g
    constructor
    · rintro ⟨x,⟨a,rfl⟩,rfl⟩
      exact ⟨a,rfl⟩
    · rintro ⟨a,rfl⟩
      exact ⟨ψ a,⟨a,rfl⟩,rfl⟩
  have hmap : (Subgroup.closure (Set.range ψ)).map H.subtype = Subgroup.closure (Set.range φ) := by
    rw [MonoidHom.map_closure,hrange]
  intro g hg
  have hh : g ∈ (Subgroup.closure (Set.range ψ)).map H.subtype := hmap.symm ▸ hg
  obtain ⟨x,hx,rfl⟩ := hh
  have hpow := Set.pow_subset_pow_right ψ.one_mem_range hr (ψ.finite_range_width hx)
  have himage : H.subtype x ∈ H.subtype '' ((Set.range ψ)^r) := ⟨x,hpow,rfl⟩
  simpa only [Set.image_pow,hrange] using himage

end DirectedCycles.GroupMultihom
