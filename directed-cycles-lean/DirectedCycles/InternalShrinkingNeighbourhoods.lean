module

public import DirectedCycles.UltraproductConjugation
public import DirectedCycles.ShrinkingGroupNeighbourhoods

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Pointwise
namespace DirectedCycles

/-- The internal fourth powers of a finite normal-neighbourhood chain
satisfy the actual shrinking and symmetry axioms in the ultraproduct. -/
def internalShrinkingNeighbourhoods {ι : Type*} (f : Filter ι)
    (G : ι → Type*) [∀ i, Group (G i)]
    (A : ∀ i, Set (G i)) (R : ℕ → ∀ i, Set (G i))
    (hAone : ∀ i, 1 ∈ A i) (hRone : ∀ n i, 1 ∈ R n i)
    (hRinv : ∀ n i, (R n i)⁻¹ = R n i)
    (hconj : ∀ n i, ∀ x ∈ (A i)^4, ∀ g ∈ (R (n+1) i)^8, x⁻¹*g*x ∈ (R n i)^4) :
    ShrinkingGroupNeighbourhoods (GroupUltraproduct f G) where
  sets := fun n => (ultraSet f G (R n))^4
  one_mem := by
    intro n
    apply Set.one_mem_pow
    rw [← map_one (ultraMk f G)]
    exact (ultraMk_mem_ultraSet_iff f G (R n) 1).mpr (Eventually.of_forall (hRone n))
  inv_eq := by
    intro n
    rw [← inv_pow,← ultraSet_inv]
    congr 2
    funext i
    exact hRinv n i
  sq_subset := by
    intro n
    rw [← pow_mul]
    change (ultraSet f G (R (n+1)))^8 ⊆ (ultraSet f G (R n))^4
    rw [← ultraSet_pow,← ultraSet_pow]
    apply ultraSet_mono
    apply Eventually.of_forall
    intro i g hg
    simpa using hconj n i 1 (Set.one_mem_pow (hAone i)) g hg

/-- Conjugation by every element of the internal fourth power respects
the internal neighbourhood chain. -/
theorem internalShrinkingNeighbourhoods_conj {ι : Type*} (f : Filter ι)
    (G : ι → Type*) [∀ i, Group (G i)]
    (A : ∀ i, Set (G i)) (R : ℕ → ∀ i, Set (G i))
    (hRone : ∀ n i, 1 ∈ R n i)
    (hconj : ∀ n i, ∀ x ∈ (A i)^4, ∀ g ∈ (R (n+1) i)^8, x⁻¹*g*x ∈ (R n i)^4)
    (n : ℕ) :
    ∀ x ∈ (ultraSet f G A)^4, ∀ g ∈ (ultraSet f G (R (n+1)))^4,
      x⁻¹*g*x ∈ (ultraSet f G (R n))^4 := by
  rw [← ultraSet_pow,← ultraSet_pow,← ultraSet_pow]
  apply ultraSet_conjugation_subset
  apply Eventually.of_forall
  intro i x hx g hg
  exact hconj n i x hx g (Set.pow_subset_pow_right (hRone (n+1) i) (by omega : 4 ≤ 8) hg)

end DirectedCycles
