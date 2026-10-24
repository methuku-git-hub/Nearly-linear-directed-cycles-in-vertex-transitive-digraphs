import DirectedCycles.ApproximateSubgroupRestriction
import DirectedCycles.QuotientPowerContainment
import DirectedCycles.CommutatorQuotients

set_option autoImplicit false
open scoped Pointwise commutatorElement
namespace DirectedCycles

/-- Precisely the weak finite abelian inverse statement needed for terminal
peeling, proved by finite_abelian_short_generation. The short generating
set must be bounded in size; an abstract rank bound alone does not suffice. -/
def FiniteAbelianShortGeneration : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ r : ℕ,
    ∀ (G : Type) [CommGroup G] [Finite G] (A : Set G),
      IsApproximateSubgroup K A → Subgroup.closure A = ⊤ →
      ∃ (H : Subgroup G) (F : Finset G),
        (H : Set G) ⊆ A^4 ∧ (F : Set G) ⊆ A^4 ∧ F.card ≤ r ∧
        Subgroup.closure ((H : Set G) ∪ (F : Set G)) = ⊤

/-- Generators modulo a subgroup killed by a surjection generate the
entire target. -/
theorem image_generators_mod_kernel {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (H : Subgroup G)
    (hH : H ≤ f.ker) (S : Set G) (hgen : Subgroup.closure ((H : Set G) ∪ S) = ⊤) :
    Subgroup.closure (f '' S) = ⊤ := by
  let T := Subgroup.closure (f '' S)
  have hpre : Subgroup.closure ((H : Set G) ∪ S) ≤ T.comap f := by
    apply (T.comap f).closure_le.mpr
    intro g hg
    rcases hg with h | h
    · change f g ∈ T
      rw [show f g = 1 from hH h]
      exact T.one_mem
    · exact Subgroup.subset_closure ⟨g,h,rfl⟩
  rw [hgen] at hpre
  apply top_unique
  intro q _
  obtain ⟨g,rfl⟩ := hf q
  exact hpre (Subgroup.mem_top g)

theorem rank_le_generators_mod_kernel {G Q : Type*} [Group G] [Group Q] [Finite Q]
    (f : G →* Q) (hf : Function.Surjective f) (H : Subgroup G)
    (hH : H ≤ f.ker) (F : Finset G)
    (hgen : Subgroup.closure ((H : Set G) ∪ (F : Set G)) = ⊤) :
    Group.rank Q ≤ F.card := by
  classical
  have he : Subgroup.closure ((F.image f : Finset Q) : Set Q) = ⊤ := by
    rw [Finset.coe_image]
    exact image_generators_mod_kernel f hf H hH (F : Set G) hgen
  exact (Group.rank_le he).trans (Finset.card_image_le)

end DirectedCycles
