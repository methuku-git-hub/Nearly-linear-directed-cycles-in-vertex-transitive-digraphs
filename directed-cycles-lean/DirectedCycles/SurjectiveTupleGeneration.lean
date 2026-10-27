module

public import DirectedCycles.CosetNilprogression

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Lifts of a generating tuple modulo K, together with the full preimage
of K, generate the source of a surjective homomorphism. -/
theorem generates_of_surjective_tuple_lifts {G H α : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (K : Subgroup H)
    (g : α → H) (u : α → G) (hu : ∀ i, f (u i) = g i)
    (hgen : Subgroup.closure ((K : Set H) ∪ Set.range g) = ⊤) :
    Subgroup.closure ((K.comap f : Set G) ∪ Set.range u) = ⊤ := by
  let S := Subgroup.closure ((K.comap f : Set G) ∪ Set.range u)
  have hK : f '' (K.comap f : Set G) = (K : Set H) := Set.image_preimage_eq _ hf
  have hu' : f '' Set.range u = Set.range g := by
    rw [← Set.range_comp']
    exact congrArg Set.range (funext hu)
  have hm : S.map f = ⊤ := by
    dsimp only [S]
    rw [MonoidHom.map_closure,Set.image_union,hK,hu',hgen]
  have hk : f.ker ≤ S := by
    intro x hx
    exact Subgroup.subset_closure (Or.inl (K.ker_le_comap f hx))
  have hh := Subgroup.comap_map_eq f S
  rw [hm,Subgroup.comap_top,sup_eq_left.mpr hk] at hh
  exact hh.symm

theorem subgroupComap_surjective_of_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (U : Subgroup H) :
    Function.Surjective (f.subgroupComap U) := by
  intro y
  obtain ⟨x,hx⟩ := hf y.val
  have hxU : x ∈ U.comap f := by
    change f x ∈ U
    rw [hx]
    exact y.property
  exact ⟨⟨x,hxU⟩,Subtype.ext hx⟩
end DirectedCycles
