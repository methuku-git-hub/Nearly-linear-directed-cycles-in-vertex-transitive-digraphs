import DirectedCycles.UniformNeighbourhoodChain
import DirectedCycles.InternalShrinkingNeighbourhoods
import DirectedCycles.UltraproductApproximateGroups

set_option autoImplicit false
open Filter
open scoped Pointwise
namespace DirectedCycles

/-- Concrete finite root sets and their uniform bounds. Existence is
proved below from the finite small-normal-neighbourhood theorem. -/
structure ApproximateRootChain {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)]
    (A : ∀ i, Finset (G i)) where
  bound : ℕ → ℝ
  density : ℕ → ℝ
  bound_one : ∀ n, 1 ≤ bound n
  density_pos : ∀ n, 0 < density n
  roots : ℕ → ∀ i, Finset (G i)
  approximate : ∀ n i, IsApproximateSubgroup (bound n) (roots n i : Set (G i))
  dense : ∀ n i, density n*(A i).card ≤ (roots n i).card
  fourth_subset : ∀ n i, (roots n i : Set (G i))^4 ⊆ (A i : Set (G i))^4
  conjugate_next : ∀ n i, ∀ x ∈ (A i : Set (G i))^4,
    ∀ g ∈ (roots (n+1) i : Set (G i))^8, x⁻¹*g*x ∈ (roots n i : Set (G i))^4

theorem exists_approximate_root_chain {ι : Type*} (G : ι → Type*)
    [∀ i, Group (G i)] [∀ i, DecidableEq (G i)] (A : ∀ i, Finset (G i))
    (K : ℝ) (hK : 1 ≤ K) (hA : ∀ i, IsApproximateSubgroup K (A i : Set (G i))) :
    Nonempty (ApproximateRootChain G A) := by
  classical
  obtain ⟨L,d,hd,hchain⟩ := FiniteAlmostPeriods.uniform_neighbourhood_chain K hK
  choose R hR using fun i => hchain (G i) (A i) (hA i)
  exact ⟨⟨L,d,fun n => (hd n).1,fun n => (hd n).2,fun n i => R i n,
    fun n i => (hR i n).1,fun n i => (hR i n).2.1,
    fun n i => (hR i n).2.2.1,fun n i => (hR i n).2.2.2⟩⟩

namespace ApproximateRootChain
variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
variable {A : ∀ i, Finset (G i)} (C : ApproximateRootChain G A)

abbrev family (n : ℕ) : ∀ i, Set (G i) := fun i => (C.roots n i : Set (G i))

def shrinking (f : Filter ι) (hAone : ∀ i, 1 ∈ A i) :
    ShrinkingGroupNeighbourhoods (GroupUltraproduct f G) :=
  internalShrinkingNeighbourhoods f G (fun i => (A i : Set (G i))) C.family hAone
    (fun n i => (C.approximate n i).one_mem) (fun n i => (C.approximate n i).inv_eq_self)
    C.conjugate_next

theorem shrinking_subset (f : Filter ι) (hAone : ∀ i, 1 ∈ A i) (n : ℕ) :
    (C.shrinking f hAone).sets n ⊆ (ultraSet f G (fun i => (A i : Set (G i))))^4 := by
  change (ultraSet f G (C.family n))^4 ⊆ _
  rw [← ultraSet_pow,← ultraSet_pow]
  exact ultraSet_mono f G _ _ (Eventually.of_forall (C.fourth_subset n))

theorem shrinking_conjugation (u : Ultrafilter ι) (hAone : ∀ i, 1 ∈ A i)
    (hAi : ∀ i, (A i : Set (G i))⁻¹ = (A i : Set (G i))) :
    Subgroup.closure (ultraSet (u : Filter ι) G (fun i => (A i : Set (G i)))) ≤
      (C.shrinking (u : Filter ι) hAone).conjugationSubgroup := by
  let B := ultraSet (u : Filter ι) G (fun i => (A i : Set (G i)))
  have hBinv : B⁻¹ = B := by
    dsimp [B]
    rw [← ultraSet_inv]
    congr 1
    funext i
    exact hAi i
  apply (C.shrinking (u : Filter ι) hAone).closure_le_conjugationSubgroup B hBinv
  intro n a ha g hg
  have hA1 : (1 : GroupUltraproduct (u : Filter ι) G) ∈ B := by
    rw [← map_one (ultraMk (u : Filter ι) G)]
    exact (ultraMk_mem_ultraSet_iff _ G _ _).mpr (Eventually.of_forall hAone)
  exact internalShrinkingNeighbourhoods_conj (u : Filter ι) G
    (fun i => (A i : Set (G i))) C.family (fun n i => (C.approximate n i).one_mem)
    C.conjugate_next n a (Set.subset_pow hA1 (by omega : 4 ≠ 0) ha) g hg

end ApproximateRootChain
end DirectedCycles
