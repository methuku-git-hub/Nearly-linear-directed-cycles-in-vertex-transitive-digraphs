module

public import DirectedCycles.UltraproductInternalSets
public import Mathlib.Combinatorics.Additive.ApproximateSubgroup
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Pointwise
namespace DirectedCycles

/-- A finite covering set can be enumerated with a fixed number of slots,
padding unused slots by the identity. -/
theorem approximate_cover_tuple {G : Type*} [Group G] (A : Set G) (K : ℝ)
    (hA : IsApproximateSubgroup K A) :
    ∃ a : Fin ⌊K⌋₊ → G, A^2 ⊆ Set.range a * A := by
  classical
  obtain ⟨F,hF,hcover⟩ := hA.sq_covBySMul
  have hcard : F.card ≤ ⌊K⌋₊ := Nat.le_floor hF
  let e := Fintype.equivFin F
  let a : Fin ⌊K⌋₊ → G := fun j =>
    if hj : j.val < Fintype.card F then (e.symm ⟨j.val,hj⟩).val else 1
  have hsub : (F : Set G) ⊆ Set.range a := by
    intro x hx
    let i := e ⟨x,hx⟩
    have hi : i.val < ⌊K⌋₊ := i.isLt.trans_le (by simpa using hcard)
    refine ⟨⟨i.val,hi⟩,?_⟩
    simp only [a,dite_eq_left i.isLt]
    change (e.symm (e ⟨x,hx⟩)).val = x
    rw [e.symm_apply_apply]
  exact ⟨a,hcover.trans (Set.mul_subset_mul_right hsub)⟩

/-- Uniform finite coverings transfer to an actual approximate subgroup
of the group ultraproduct. -/
theorem ultraSet_approximate_of_cover_tuple {ι J : Type*} [Fintype J]
    (u : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (A : ∀ i, Set (G i)) (h1 : ∀ i, 1 ∈ A i) (hi : ∀ i, (A i)⁻¹ = A i)
    (a : J → ∀ i, G i) (hcover : ∀ i, A i^2 ⊆ Set.range (fun j => a j i) * A i) :
    IsApproximateSubgroup (Fintype.card J : ℝ) (ultraSet (u : Filter ι) G A) := by
  classical
  let f : Filter ι := u
  let F := Finset.univ.image (fun j => ultraMk f G (a j))
  refine ⟨?_,?_,F,?_,?_⟩
  · rw [← map_one (ultraMk f G)]
    exact (ultraMk_mem_ultraSet_iff f G A 1).mpr (Eventually.of_forall h1)
  · rw [← ultraSet_inv]
    congr 1
    funext i
    exact hi i
  · exact_mod_cast (Finset.card_image_le : F.card ≤ Finset.univ.card)
  · change ultraSet f G A ^ 2 ⊆ (F : Set (GroupUltraproduct f G)) * ultraSet f G A
    have hh := ultraSet_mono f G (fun i => A i^2)
      (fun i => Set.range (fun j => a j i)*A i) (Eventually.of_forall hcover)
    rw [ultraSet_pow,ultraSet_mul,ultraSet_finite_range] at hh
    simpa only [F,Finset.coe_image,Finset.coe_univ,Set.image_univ] using hh

/-- A family of K-approximate subgroups gives a K-approximate internal
subset of the actual ultraproduct group. No finiteness of the ultraproduct
set is asserted. -/
theorem ultraSet_isApproximate {ι : Type*} (u : Ultrafilter ι)
    (G : ι → Type*) [∀ i, Group (G i)] (A : ∀ i, Set (G i)) (K : ℝ) (hK : 1 ≤ K)
    (hA : ∀ i, IsApproximateSubgroup K (A i)) :
    IsApproximateSubgroup K (ultraSet (u : Filter ι) G A) := by
  classical
  choose a ha using fun i => approximate_cover_tuple (A i) K (hA i)
  have hh := ultraSet_approximate_of_cover_tuple u G A (fun i => (hA i).one_mem)
    (fun i => (hA i).inv_eq_self) (fun j i => a i j) ha
  have hfloor : (⌊K⌋₊ : ℝ) ≤ K := Nat.floor_le (by linarith)
  exact IsApproximateSubgroup.mono (by simpa using hfloor) hh

end DirectedCycles
