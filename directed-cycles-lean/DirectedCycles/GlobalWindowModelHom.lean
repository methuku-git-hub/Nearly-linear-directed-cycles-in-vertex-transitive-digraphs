import DirectedCycles.WindowUltraproductEquiv
import DirectedCycles.LocalGroupHom
import DirectedCycles.LocalInternalSetLogic

set_option autoImplicit false
namespace DirectedCycles

def LocalGroupHom.ofMonoidHom {G H : Type*} [Group G] [Group H] (f : G →* H) :
    LocalGroupHom (LocalGroupAlgebra.ofGroup G) (LocalGroupAlgebra.ofGroup H) where
  toFun := f
  map_one := _root_.map_one f
  map_inv := _root_.map_inv f
  map_mul := by
    intro x y z h
    change f x*f y = f z
    rw [← _root_.map_mul,h]

variable {ι : Type*} (F : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (W : ∀ i, Set (G i)) (h1 : ∀ i, (1 : G i) ∈ W i)
    (hi : ∀ i, ∀ x ∈ W i, x⁻¹ ∈ W i)

/-- The actual local reduced product of finite windows maps into the global
group reduced product, preserving every defined product. -/
def ultraWindowGroupHom :
    LocalGroupHom
      (localUltraAlgebra F (fun i => W i)
        (fun i => (LocalGroupAlgebra.ofGroup (G i)).restrict (W i) (h1 i) (hi i)))
      (LocalGroupAlgebra.ofGroup (GroupUltraproduct F G)) where
  toFun x := (ultraWindowMap F G W x).val
  map_one := map_one (ultraMk F G)
  map_inv := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact map_inv (ultraMk F G) (fun i => (a i).val)
  map_mul := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c h
    have hh := (localUltraMulRel_mk_iff F (fun i => W i)
      (fun i => (LocalGroupAlgebra.ofGroup (G i)).restrict (W i) (h1 i) (hi i)) a b c).1 h
    change ultraMk F G (fun i => (a i).val)*ultraMk F G (fun i => (b i).val) =
      ultraMk F G (fun i => (c i).val)
    rw [← map_mul]
    exact (ultraMk_eq_iff F G _ _).2 hh

theorem ultraWindowGroupHom_injective :
    Function.Injective (ultraWindowGroupHom F G W h1 hi).toFun := by
  intro x y h
  exact ultraWindowMap_injective F G W (Subtype.ext h)

theorem ultraWindowGroupHom_range :
    Set.range (ultraWindowGroupHom F G W h1 hi).toFun = ultraSet F G W := by
  apply Set.Subset.antisymm
  · rintro x ⟨y,rfl⟩
    exact (ultraWindowMap F G W y).property
  · intro x hx
    obtain ⟨y,hy⟩ := ultraWindowMap_surjective F G W h1 ⟨x,hx⟩
    exact ⟨y,congrArg Subtype.val hy⟩

/-- Internal preimages are literal component preimages, including on
exceptional indices where the ambient internal set leaves the window. -/
theorem ultraWindowGroupHom_internal_preimage (B : ∀ i, Set (G i)) :
    (ultraWindowGroupHom F G W h1 hi).toFun ⁻¹' ultraSet F G B =
      localUltraSet F (fun i => W i) (fun i => Subtype.val ⁻¹' B i) := by
  ext x
  refine Quotient.inductionOn x ?_
  intro a
  change ultraMk F G (fun i => (a i).val) ∈ ultraSet F G B ↔
    localUltraMk F (fun i => W i) a ∈ localUltraSet F (fun i => W i) (fun i => Subtype.val ⁻¹' B i)
  rw [ultraMk_mem_ultraSet_iff,localUltraMk_mem_iff]
  rfl

/-- A model on an actual ambient subgroup induces a model homomorphism on
any internal finite window lying in that subgroup. -/
def ultraWindowSubgroupHom (S : Subgroup (GroupUltraproduct F G))
    (hWS : ultraSet F G W ⊆ S) :
    LocalGroupHom
      (localUltraAlgebra F (fun i => W i)
        (fun i => (LocalGroupAlgebra.ofGroup (G i)).restrict (W i) (h1 i) (hi i)))
      (LocalGroupAlgebra.ofGroup S) where
  toFun x := ⟨(ultraWindowGroupHom F G W h1 hi).toFun x,hWS (ultraWindowMap F G W x).property⟩
  map_one := Subtype.ext (ultraWindowGroupHom F G W h1 hi).map_one
  map_inv x := Subtype.ext ((ultraWindowGroupHom F G W h1 hi).map_inv x)
  map_mul h := Subtype.ext ((ultraWindowGroupHom F G W h1 hi).map_mul h)

def ultraWindowModelHom {H : Type*} [Group H]
    (S : Subgroup (GroupUltraproduct F G)) (hWS : ultraSet F G W ⊆ S) (π : S →* H) :=
  (LocalGroupHom.ofMonoidHom π).comp (ultraWindowSubgroupHom F G W h1 hi S hWS)

theorem ultraWindowModelHom_apply {H : Type*} [Group H]
    (S : Subgroup (GroupUltraproduct F G)) (hWS : ultraSet F G W ⊆ S) (π : S →* H)
    (x : LocalUltraproduct F (fun i => W i)) :
    (ultraWindowModelHom F G W h1 hi S hWS π).toFun x =
      π ⟨(ultraWindowMap F G W x).val,hWS (ultraWindowMap F G W x).property⟩ := rfl
end DirectedCycles
