module

public import DirectedCycles.GroupUltraproduct
public import DirectedCycles.LocalGroupUltraproduct

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (W : ∀ i, Set (G i))

/-- Reduced products of component windows are identified with the actual
internal window in the group reduced product. -/
def ultraWindowMap : LocalUltraproduct F (fun i => W i) → ultraSet F G W :=
  Quotient.lift (fun a => ⟨ultraMk F G (fun i => (a i).val),
    (ultraMk_mem_ultraSet_iff F G W _).2 (Filter.Eventually.of_forall fun i => (a i).property)⟩) (by
      intro a b hab
      apply Subtype.ext
      apply (ultraMk_eq_iff F G _ _).2
      exact hab.mono fun _ hi => congrArg Subtype.val hi)

theorem ultraWindowMap_injective : Function.Injective (ultraWindowMap F G W) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b he
  apply (localUltraMk_eq_iff F (fun i => W i) a b).2
  have hv := congrArg Subtype.val he
  have hh := (ultraMk_eq_iff F G (fun i => (a i).val) (fun i => (b i).val)).1 hv
  exact hh.mono fun _ hi => Subtype.ext hi

theorem ultraWindowMap_surjective (h1 : ∀ i, (1 : G i) ∈ W i) :
    Function.Surjective (ultraWindowMap F G W) := by
  classical
  intro x
  obtain ⟨v,hv⟩ := ultraMk_surjective F G x.val
  have hvW : ∀ᶠ i in F, v i ∈ W i := (ultraMk_mem_ultraSet_iff F G W v).1 (hv.symm ▸ x.property)
  let a : ∀ i, W i := fun i => if hi : v i ∈ W i then ⟨v i,hi⟩ else ⟨1,h1 i⟩
  refine ⟨localUltraMk F (fun i => W i) a,?_⟩
  apply Subtype.ext
  change ultraMk F G (fun i => (a i).val) = x.val
  rw [← hv]
  apply (ultraMk_eq_iff F G _ _).2
  filter_upwards [hvW] with i hi
  dsimp only [a]
  rw [dite_eq_left hi]

noncomputable def ultraWindowEquiv (h1 : ∀ i, (1 : G i) ∈ W i) :
    LocalUltraproduct F (fun i => W i) ≃ ultraSet F G W :=
  Equiv.ofBijective (ultraWindowMap F G W)
    ⟨ultraWindowMap_injective F G W,ultraWindowMap_surjective F G W h1⟩
end DirectedCycles
