import DirectedCycles.LocalQuotientWindow
import DirectedCycles.UltraproductInternalSets

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]

/-- Local normality, including its exact domain restrictions, transfers from
the components to the actual internal sets in the group reduced product. -/
theorem ultraSet_localNormal (P V : ∀ i, Set (G i))
    (hP : ∀ᶠ i in F, LocalNormalSet (P i) (V i)) :
    LocalNormalSet (ultraSet F G P) (ultraSet F G V) where
  one_mem := by
    rw [← map_one (ultraMk F G)]
    exact (ultraMk_mem_ultraSet_iff F G P _).2 (hP.mono fun _ hi => hi.one_mem)
  inv_mem := by
    intro x hx
    obtain ⟨a,rfl⟩ := ultraMk_surjective F G x
    have ha := (ultraMk_mem_ultraSet_iff F G P a).1 hx
    rw [← map_inv]
    apply (ultraMk_mem_ultraSet_iff F G P _).2
    filter_upwards [hP,ha] with i hPi hai
    exact hPi.inv_mem _ hai
  mul_mem := by
    intro x hx y hy hxy
    obtain ⟨a,rfl⟩ := ultraMk_surjective F G x
    obtain ⟨b,rfl⟩ := ultraMk_surjective F G y
    have ha := (ultraMk_mem_ultraSet_iff F G P a).1 hx
    have hb := (ultraMk_mem_ultraSet_iff F G P b).1 hy
    rw [← map_mul] at hxy ⊢
    have hab := (ultraMk_mem_ultraSet_iff F G V (a*b)).1 hxy
    apply (ultraMk_mem_ultraSet_iff F G P _).2
    filter_upwards [hP,ha,hb,hab] with i hPi hai hbi habi
    exact hPi.mul_mem _ hai _ hbi habi
  conj_mem := by
    intro x hx p hp hconj
    obtain ⟨a,rfl⟩ := ultraMk_surjective F G x
    obtain ⟨b,rfl⟩ := ultraMk_surjective F G p
    have ha := (ultraMk_mem_ultraSet_iff F G V a).1 hx
    have hb := (ultraMk_mem_ultraSet_iff F G P b).1 hp
    rw [← map_inv,← map_mul,← map_mul] at hconj ⊢
    have hab := (ultraMk_mem_ultraSet_iff F G V (a*b*a⁻¹)).1 hconj
    apply (ultraMk_mem_ultraSet_iff F G P _).2
    filter_upwards [hP,ha,hb,hab] with i hPi hai hbi habi
    exact hPi.conj_mem _ hai _ hbi habi

/-- Symmetric window and sixth-power containment transfer as actual internal
set identities and inclusions. -/
theorem ultraSet_quotient_window (W V : ∀ i, Set (G i))
    (h1 : ∀ᶠ i in F, (1 : G i) ∈ W i)
    (hi : ∀ᶠ i in F, (W i)⁻¹ = W i)
    (h6 : ∀ᶠ i in F, (W i)^6 ⊆ V i) :
    (1 : GroupUltraproduct F G) ∈ ultraSet F G W ∧
      (ultraSet F G W)⁻¹ = ultraSet F G W ∧ (ultraSet F G W)^6 ⊆ ultraSet F G V := by
  refine ⟨?_,?_,?_⟩
  · rw [← map_one (ultraMk F G)]
    exact (ultraMk_mem_ultraSet_iff F G W _).2 h1
  · rw [← ultraSet_inv]
    apply Set.Subset.antisymm
    · apply ultraSet_mono F G
      exact hi.mono fun _ he => he.subset
    · apply ultraSet_mono F G
      exact hi.mono fun _ he => he.symm.subset
  · rw [← ultraSet_pow]
    exact ultraSet_mono F G _ _ h6
end DirectedCycles
