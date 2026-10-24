import DirectedCycles.GlobalKernelWindowLocalModel
import DirectedCycles.LocalApproximateFiniteTransfer

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles.GlobalGoodModelKernelWindows
variable {u : Ultrafilter ℕ} {G : ℕ → Type*} [∀ i, Group (G i)] [∀ i, DecidableEq (G i)]
    {A : ∀ i, Finset (G i)}
    {M : let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
      let H := Subgroup.closure B
      InternalLocallyCompactGroupModel H (H.subtype ⁻¹' (B^4)) (IsInternalFiniteIn u G H)}
    {D : LieQuotientData M.carrier M.neighbourhood}
    (C : GlobalGoodModelKernelWindows u G A M D)

 theorem source_one (i : ℕ) : (C.windowAlgebra i).one ∈ C.finiteSource i := by
  change (C.windowAlgebra i).one ∈ (C.finiteSource i : Set (C.W i : Set (G i)))
  rw [finiteSource,finiteWindowSource_coe]
  exact (C.B_data i).1

 theorem source_inv (i : ℕ) : ∀ x ∈ C.finiteSource i, (C.windowAlgebra i).inv x ∈ C.finiteSource i := by
  intro x hx
  change x ∈ (C.finiteSource i : Set (C.W i : Set (G i))) at hx
  change (C.windowAlgebra i).inv x ∈ (C.finiteSource i : Set (C.W i : Set (G i)))
  rw [finiteSource,finiteWindowSource_coe] at hx ⊢
  exact (C.B_data i).2.1 x.val hx

 theorem source_binary_domains : ∀ᶠ i in (u : Filter ℕ),
    (C.windowAlgebra i).AllProductsDefined (C.finiteSource i : Set (C.W i : Set (G i))) 2 := by
  filter_upwards [C.products] with i hi
  exact finite_window_binary_domains (C.W i : Set (G i)) (C.W_data i).1 (C.W_data i).2.1
    (C.B i) (C.B_data i).1 hi

 theorem source_density : ∃ J : ℕ, 1 ≤ J ∧ ∀ᶠ i in (u : Filter ℕ),
    (A i).card ≤ J*(C.finiteSource i).card := by
  obtain ⟨J,hJ,hcard⟩ := C.density
  refine ⟨J,hJ,?_⟩
  filter_upwards [hcard,C.products] with i hi hpi
  have he := finite_window_card_of_square (C.W i : Set (G i)) (C.B i) (C.B_data i).1 hpi
  simpa only [finiteSource,he] using hi

 theorem source_division (i : ℕ) : (C.windowAlgebra i).DivisionClosed :=
  (LocalGroupAlgebra.ofGroup_divisionClosed (G i)).restrict (LocalGroupAlgebra.ofGroup (G i))
    (C.W i : Set (G i)) (C.W_data i).1 (C.W_data i).2.1

 theorem source_reversible (i : ℕ) : (C.windowAlgebra i).Reversible := by
  have h : (LocalGroupAlgebra.ofGroup (G i)).Reversible := LocalGroupAlgebra.ofGroup_reversible (G i)
  intro x y z hxyz
  exact h.restrict (LocalGroupAlgebra.ofGroup (G i)) (C.W i : Set (G i)) (C.W_data i).1 (C.W_data i).2.1 hxyz
end DirectedCycles.GlobalGoodModelKernelWindows
