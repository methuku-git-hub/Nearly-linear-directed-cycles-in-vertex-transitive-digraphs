import DirectedCycles.ZeroEscapeSubgroup
import DirectedCycles.UltraproductSubgroups

set_option autoImplicit false
open Filter
open scoped Pointwise
namespace DirectedCycles

/-- A family of finite strong approximate groups has an actual internal
zero-escape subgroup, normalized by the internal tenth power. No saturation
or transfer principle is assumed for this statement. -/
theorem internal_zero_escape_subgroup {ι : Type*} (f : Filter ι) (G : ι → Type*)
    [∀ i, Group (G i)] [∀ i, Fintype (G i)] (K : ℕ) (A : ∀ i, Finset (G i))
    (hA : ∀ i, IsStrongFiniteApproximateGroup K (A i)) :
    ∃ H : ∀ i, Subgroup (G i),
      (∀ i g, g ∈ H i ↔ escapeNorm (A i : Set (G i)) g = 0) ∧
      (∀ i, (H i : Set (G i)) ⊆ A i) ∧
      (∀ x : ∀ i, G i, ultraMk f G x ∈ ultraSubgroup f G H ↔
        ∀ᶠ i in f, escapeNorm (A i : Set (G i)) (x i) = 0) ∧
      (ultraSubgroup f G H : Set (GroupUltraproduct f G)) ⊆
        ultraSet f G (fun i => (A i : Set (G i))) ∧
      (ultraSet f G (fun i => (A i : Set (G i))))^10 ⊆
        Subgroup.normalizer (ultraSubgroup f G H : Set (GroupUltraproduct f G)) := by
  classical
  choose H hmem hsub hnormal using fun i => strong_approximate_zero_subgroup (hA i)
  refine ⟨H,hmem,hsub,?_,?_,?_⟩
  · intro x
    rw [mem_ultraSubgroup_iff]
    simp only [hmem]
  · exact ultraSet_mono f G _ _ (Filter.Eventually.of_forall hsub)
  · rw [← ultraSet_pow]
    exact ultraSubgroup_normalizer f G H (fun i => (A i : Set (G i))^10)
      (Filter.Eventually.of_forall hnormal)
end DirectedCycles
