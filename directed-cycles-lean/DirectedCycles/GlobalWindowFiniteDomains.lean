import DirectedCycles.LocalProductRestriction
import DirectedCycles.LocalProductDomainTransfer
import DirectedCycles.LocalGlobalWordPowers

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

noncomputable def finiteWindowSource {G : Type*} (W : Set G) (A : Finset G) : Finset W := by
  classical
  exact A.subtype (fun x => x ∈ W)

theorem finiteWindowSource_coe {G : Type*} (W : Set G) (A : Finset G) :
    (finiteWindowSource W A : Set W) = Subtype.val ⁻¹' (A : Set G) := by
  classical
  ext x
  simp only [finiteWindowSource,Finset.mem_coe,Finset.mem_subtype,Set.mem_preimage]

theorem finiteWindowSource_card {G : Type*} (W : Set G) (A : Finset G)
    (hAW : (A : Set G) ⊆ W) : (finiteWindowSource W A).card = A.card := by
  classical
  rw [finiteWindowSource,Finset.card_subtype,Finset.filter_eq_self.mpr hAW]

/-- A component square contained in the actual source window certifies all
binary local products, including their subproducts. -/
theorem finite_window_binary_domains {G : Type*} [Group G] (W : Set G)
    (hW1 : (1 : G) ∈ W) (hWi : ∀ x ∈ W, x⁻¹ ∈ W) (A : Finset G)
    (hA1 : (1 : G) ∈ A) (hAW : (A : Set G)^2 ⊆ W) :
    ((LocalGroupAlgebra.ofGroup G).restrict W hW1 hWi).AllProductsDefined
      (finiteWindowSource W A : Set W) 2 := by
  rw [finiteWindowSource_coe]
  apply LocalGroupAlgebra.allProductsDefined_restrict
    (LocalGroupAlgebra.ofGroup G) W hW1 hWi
    (LocalGroupAlgebra.ofGroup_allProductsDefined (A : Set G) 2)
  intro n hn
  rw [LocalGroupAlgebra.ofGroup_wordPower]
  exact (Set.pow_subset_pow_right hA1 hn).trans hAW

/-- The exact finite source has the original cardinality on every component
whose square lies in the ambient window. -/
theorem finite_window_card_of_square {G : Type*} [Group G] (W : Set G) (A : Finset G)
    (hA1 : (1 : G) ∈ A) (hAW : (A : Set G)^2 ⊆ W) :
    (finiteWindowSource W A).card = A.card :=
  finiteWindowSource_card W A ((Set.subset_pow hA1 (by omega : 2 ≠ 0)).trans hAW)
end DirectedCycles
