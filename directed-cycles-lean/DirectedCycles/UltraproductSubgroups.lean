module

public import DirectedCycles.UltraproductInternalSets

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Pointwise
namespace DirectedCycles

/-- An actual subgroup of the group ultraproduct from a family of subgroups. -/
noncomputable def ultraSubgroup {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) : Subgroup (GroupUltraproduct f G) where
  carrier := ultraSet f G (fun i => (H i : Set (G i)))
  one_mem' := by
    rw [← (ultraMk f G).map_one]
    exact (ultraMk_mem_ultraSet_iff f G _ 1).2 (Filter.Eventually.of_forall (fun i => (H i).one_mem))
  mul_mem' := by
    intro a b ha hb
    obtain ⟨x,rfl⟩ := ultraMk_surjective f G a
    obtain ⟨y,rfl⟩ := ultraMk_surjective f G b
    rw [← map_mul]
    apply (ultraMk_mem_ultraSet_iff f G _ (x*y)).2
    have hx := (ultraMk_mem_ultraSet_iff f G _ x).1 ha
    have hy := (ultraMk_mem_ultraSet_iff f G _ y).1 hb
    filter_upwards [hx,hy] with i hi hj
    exact (H i).mul_mem hi hj
  inv_mem' := by
    intro a ha
    obtain ⟨x,rfl⟩ := ultraMk_surjective f G a
    rw [← map_inv]
    apply (ultraMk_mem_ultraSet_iff f G _ x⁻¹).2
    have hx := (ultraMk_mem_ultraSet_iff f G _ x).1 ha
    filter_upwards [hx] with i hi
    exact (H i).inv_mem hi

@[simp] theorem mem_ultraSubgroup_iff {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) (x : ∀ i, G i) :
    ultraMk f G x ∈ ultraSubgroup f G H ↔ ∀ᶠ i in f, x i ∈ H i :=
  ultraMk_mem_ultraSet_iff f G _ x

theorem ultraSubgroup_normalizer {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) (B : ∀ i, Set (G i))
    (hB : ∀ᶠ i in f, B i ⊆ Subgroup.normalizer (H i : Set (G i))) :
    ultraSet f G B ⊆ Subgroup.normalizer (ultraSubgroup f G H : Set (GroupUltraproduct f G)) := by
  intro b hb
  obtain ⟨y,rfl⟩ := ultraMk_surjective f G b
  have hy := (ultraMk_mem_ultraSet_iff f G B y).1 hb
  apply Subgroup.mem_set_normalizer_iff''.2
  intro a
  obtain ⟨x,rfl⟩ := ultraMk_surjective f G a
  rw [← map_inv, ← map_mul, ← map_mul]
  change ultraMk f G x ∈ ultraSubgroup f G H ↔ ultraMk f G (y⁻¹*x*y) ∈ ultraSubgroup f G H
  rw [mem_ultraSubgroup_iff, mem_ultraSubgroup_iff]
  constructor
  · intro hx
    filter_upwards [hB,hy,hx] with i hBi hyi hxi
    exact (Subgroup.mem_normalizer_iff''.1 (hBi hyi) (x i)).1 hxi
  · intro hx
    filter_upwards [hB,hy,hx] with i hBi hyi hxi
    exact (Subgroup.mem_normalizer_iff''.1 (hBi hyi) (x i)).2 hxi
end DirectedCycles
