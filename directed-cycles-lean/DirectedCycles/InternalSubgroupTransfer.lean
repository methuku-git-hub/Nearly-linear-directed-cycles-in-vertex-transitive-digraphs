module

public import DirectedCycles.UltraproductSubgroups
public import DirectedCycles.InternalSetLogic

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Pointwise
namespace DirectedCycles

/-- An actual subgroup whose carrier is internal is an ultraproduct of actual
component subgroups. Bad indices are filled with the trivial subgroup. -/
theorem subgroup_components_of_internal {ι : Type*} (u : Ultrafilter ι)
    (G : ι → Type*) [∀ i, Group (G i)]
    (H : Subgroup (GroupUltraproduct (u : Filter ι) G)) (A : ∀ i, Set (G i))
    (hA : (H : Set _) = ultraSet (u : Filter ι) G A) :
    ∃ B : ∀ i, Subgroup (G i), ultraSubgroup (u : Filter ι) G B = H ∧
      ∀ᶠ i in (u : Filter ι), (B i : Set (G i)) = A i := by
  classical
  have h1 : ∀ᶠ i in (u : Filter ι), (1 : G i) ∈ A i := by
    apply (ultraMk_mem_ultraSet_iff _ G A 1).1
    rw [map_one,← hA]
    exact H.one_mem
  have hi : ∀ᶠ i in (u : Filter ι), (A i)⁻¹ ⊆ A i := by
    apply (ultraSet_subset_iff_eventually u G _ _).1
    rw [ultraSet_inv,← hA]
    intro x hx
    have hx' : x⁻¹ ∈ H := hx
    change x ∈ H
    simpa only [inv_inv] using H.inv_mem hx'
  have hm : ∀ᶠ i in (u : Filter ι), A i*A i ⊆ A i := by
    apply (ultraSet_subset_iff_eventually u G _ _).1
    rw [ultraSet_mul,← hA]
    rintro x ⟨a,ha,b,hb,rfl⟩
    exact H.mul_mem ha hb
  let Good := fun i => (1 : G i) ∈ A i ∧
    (∀ x ∈ A i, x⁻¹ ∈ A i) ∧ (∀ x ∈ A i, ∀ y ∈ A i, x*y ∈ A i)
  have hg : ∀ᶠ i in (u : Filter ι), Good i := by
    filter_upwards [h1,hi,hm] with i h1i hii hmi
    exact ⟨h1i,fun x hx => hii (Set.inv_mem_inv.mpr hx),
      fun x hx y hy => hmi (Set.mul_mem_mul hx hy)⟩
  let B : ∀ i, Subgroup (G i) := fun i => if h : Good i then
    { carrier := A i
      one_mem' := h.1
      inv_mem' := fun {x} hx => h.2.1 x hx
      mul_mem' := fun {x y} hx hy => h.2.2 x hx y hy } else ⊥
  have he : ∀ᶠ i in (u : Filter ι), (B i : Set (G i)) = A i := by
    filter_upwards [hg] with i hi
    dsimp only [B]
    rw [dite_eq_left hi]
    rfl
  refine ⟨B,?_,he⟩
  apply SetLike.coe_injective
  change ultraSet (u : Filter ι) G (fun i => (B i : Set (G i))) = (H : Set _)
  rw [hA]
  exact (ultraSet_eq_iff_eventually u G _ _).2 he
end DirectedCycles
