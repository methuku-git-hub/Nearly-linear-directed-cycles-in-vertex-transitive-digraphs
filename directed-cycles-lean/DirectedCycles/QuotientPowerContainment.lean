module

public import DirectedCycles.FiniteStructuralAlgebra

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Pulling back a power of an image costs one kernel factor. -/
theorem preimage_image_pow_subset {G A : Type*} [Group G] [Group A]
    (f : G →* A) (S : Set G) (m k : ℕ) (hker : (f.ker : Set G) ⊆ S^k) :
    f ⁻¹' ((f '' S)^m) ⊆ S^(m+k) := by
  intro g hg
  rw [← Set.image_pow] at hg
  obtain ⟨a,ha,he⟩ := hg
  have hmem : a⁻¹*g ∈ f.ker := by
    change f (a⁻¹*g) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  rw [pow_add]
  exact ⟨a,ha,a⁻¹*g,hker hmem,mul_inv_cancel_left _ _⟩

theorem image_generating_set {G A : Type*} [Group G] [Group A]
    (f : G →* A) (hf : Function.Surjective f) (S : Set G)
    (hS : Subgroup.closure S = ⊤) : Subgroup.closure (f '' S) = ⊤ := by
  rw [← MonoidHom.map_closure,hS,Subgroup.map_top_of_surjective f hf]

/-- The preimage of the normal envelope of a stabilizer intersection
contains every corresponding point stabilizer and stays in N. -/
theorem quotient_stabilizer_envelope {G A V : Type*} [Group G] [Group A] [MulAction G V]
    (f : G →* A) (hf : Function.Surjective f) (N : Subgroup G) [N.Normal]
    (hker : f.ker ≤ N) (e : V) (ht : ∀ x y : V, ∃ g : G, g • x = y) :
    let J := (N ⊓ MulAction.stabilizer G e).map f
    let L := (Subgroup.normalClosure (J : Set A)).comap f
    f.ker ≤ L ∧ L ≤ N ∧ ∀ x : V, N ⊓ MulAction.stabilizer G x ≤ L := by
  let J := (N ⊓ MulAction.stabilizer G e).map f
  let L := (Subgroup.normalClosure (J : Set A)).comap f
  let : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hJN : J ≤ N.map f := Subgroup.map_mono inf_le_left
  have hLN : L ≤ N := by
    have hcl : Subgroup.normalClosure (J : Set A) ≤ N.map f :=
      Subgroup.normalClosure_le_normal hJN
    have hh := Subgroup.comap_mono (f := f) hcl
    rw [Subgroup.comap_map_eq_self hker] at hh
    exact hh
  have hbase : N ⊓ MulAction.stabilizer G e ≤ L := by
    intro g hg
    exact Subgroup.subset_normalClosure (Subgroup.mem_map_of_mem f hg)
  have hclosure : stabilizerClosure N e ≤ L := Subgroup.normalClosure_le_normal hbase
  exact ⟨Subgroup.ker_le_comap f _,hLN,fun x => (normal_stabilizer_le_closure N e ht x).trans hclosure⟩

end DirectedCycles
