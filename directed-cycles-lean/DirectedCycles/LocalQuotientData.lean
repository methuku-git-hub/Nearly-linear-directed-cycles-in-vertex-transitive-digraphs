import DirectedCycles.LocalQuotientCancellation
import DirectedCycles.UltraproductLocalNormal

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Data and proofs defining an actual local window quotient. -/
structure LocalQuotientData (G : Type*) [Group G] where
  P : Set G
  V : Set G
  W : Set G
  localNormal : LocalNormalSet P V
  one_mem : (1 : G) ∈ W
  inv_eq : W⁻¹ = W
  sixth_subset : W^6 ⊆ V

namespace LocalQuotientData
variable {G : Type*} [Group G] (D : LocalQuotientData G)
abbrev Carrier := D.localNormal.WindowQuotient D.one_mem D.inv_eq D.sixth_subset
abbrev algebra : LocalGroupAlgebra D.Carrier :=
  D.localNormal.quotientAlgebra D.one_mem D.inv_eq D.sixth_subset
abbrev project (a : D.W) : D.Carrier := D.localNormal.windowMk D.one_mem D.inv_eq D.sixth_subset a

theorem project_eq_iff (a b : D.W) : D.project a = D.project b ↔ a.val*b.val⁻¹ ∈ D.P :=
  D.localNormal.window_quotient_eq_iff D.one_mem D.inv_eq D.sixth_subset a b

abbrev ultraproduct {ι : Type*} (F : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (D : ∀ i, LocalQuotientData (G i)) : LocalQuotientData (GroupUltraproduct F G) where
  P := ultraSet F G (fun i => (D i).P)
  V := ultraSet F G (fun i => (D i).V)
  W := ultraSet F G (fun i => (D i).W)
  localNormal := ultraSet_localNormal F G _ _ (Filter.Eventually.of_forall fun i => (D i).localNormal)
  one_mem := (ultraSet_quotient_window F G _ _ (Filter.Eventually.of_forall fun i => (D i).one_mem)
    (Filter.Eventually.of_forall fun i => (D i).inv_eq) (Filter.Eventually.of_forall fun i => (D i).sixth_subset)).1
  inv_eq := (ultraSet_quotient_window F G _ _ (Filter.Eventually.of_forall fun i => (D i).one_mem)
    (Filter.Eventually.of_forall fun i => (D i).inv_eq) (Filter.Eventually.of_forall fun i => (D i).sixth_subset)).2.1
  sixth_subset := (ultraSet_quotient_window F G _ _ (Filter.Eventually.of_forall fun i => (D i).one_mem)
    (Filter.Eventually.of_forall fun i => (D i).inv_eq) (Filter.Eventually.of_forall fun i => (D i).sixth_subset)).2.2
end LocalQuotientData
end DirectedCycles
