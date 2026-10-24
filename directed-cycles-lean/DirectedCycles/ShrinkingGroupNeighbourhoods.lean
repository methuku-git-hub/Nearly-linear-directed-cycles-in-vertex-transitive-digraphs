import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Tactic

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- A countable shrinking family. This is data for a topology, not an
existence assertion or an assumed compact/Lie model. -/
structure ShrinkingGroupNeighbourhoods (G : Type*) [Group G] where
  sets : ℕ → Set G
  one_mem : ∀ n, 1 ∈ sets n
  inv_eq : ∀ n, (sets n)⁻¹ = sets n
  sq_subset : ∀ n, (sets (n+1))^2 ⊆ sets n

namespace ShrinkingGroupNeighbourhoods
variable {G : Type*} [Group G] (S : ShrinkingGroupNeighbourhoods G)

theorem succ_subset (n : ℕ) : S.sets (n+1) ⊆ S.sets n := by
  exact (Set.subset_pow (S.one_mem (n+1)) (by omega : 2 ≠ 0)).trans (S.sq_subset n)

theorem antitone : Antitone S.sets := antitone_nat_of_succ_le S.succ_subset

def ConjugationContinuous (g : G) : Prop :=
  ∀ n, ∃ m, ∀ x ∈ S.sets m, g*x*g⁻¹ ∈ S.sets n

theorem conjugationContinuous_one : S.ConjugationContinuous 1 := by
  intro n
  exact ⟨n,by simp⟩

theorem ConjugationContinuous.mul {g h : G}
    (hg : S.ConjugationContinuous g) (hh : S.ConjugationContinuous h) :
    S.ConjugationContinuous (g*h) := by
  intro n
  obtain ⟨m,hm⟩ := hg n
  obtain ⟨k,hk⟩ := hh m
  refine ⟨k,?_⟩
  intro x hx
  have := hm (h*x*h⁻¹) (hk x hx)
  convert this using 1
  group

/-- Elements whose conjugation and inverse conjugation preserve the
neighbourhood filter form an actual subgroup. -/
def conjugationSubgroup : Subgroup G where
  carrier := {g | S.ConjugationContinuous g ∧ S.ConjugationContinuous g⁻¹}
  one_mem' := by
    change S.ConjugationContinuous 1 ∧ S.ConjugationContinuous (1 : G)⁻¹
    simpa only [inv_one] using And.intro S.conjugationContinuous_one S.conjugationContinuous_one
  mul_mem' := by
    intro g h hg hh
    exact ⟨hg.1.mul S hh.1,by simpa only [mul_inv_rev] using hh.2.mul S hg.2⟩
  inv_mem' := by
    intro g hg
    change S.ConjugationContinuous g⁻¹ ∧ S.ConjugationContinuous (g⁻¹)⁻¹
    simpa only [inv_inv] using hg.symm

theorem closure_le_conjugationSubgroup (A : Set G) (hAinv : A⁻¹ = A)
    (hconj : ∀ n, ∀ a ∈ A, ∀ x ∈ S.sets (n+1), a⁻¹*x*a ∈ S.sets n) :
    Subgroup.closure A ≤ S.conjugationSubgroup := by
  apply (S.conjugationSubgroup).closure_le.mpr
  intro a ha
  have hai : a⁻¹ ∈ A := by
    have : a⁻¹ ∈ A⁻¹ := by simpa using ha
    simpa only [hAinv] using this
  constructor
  · intro n
    refine ⟨n+1,?_⟩
    intro x hx
    simpa only [inv_inv] using hconj n a⁻¹ hai x hx
  · intro n
    exact ⟨n+1,by simpa only [inv_inv] using hconj n a ha⟩

/-- The group topology on any subgroup on which conjugation is continuous
for the shrinking family. -/
@[instance_reducible]
def subgroupFilterBasis (H : Subgroup G) (hH : H ≤ S.conjugationSubgroup) : GroupFilterBasis H where
  sets := Set.range (fun n => H.subtype ⁻¹' S.sets n)
  nonempty := ⟨_,⟨0,rfl⟩⟩
  inter_sets := by
    rintro U V ⟨m,rfl⟩ ⟨n,rfl⟩
    refine ⟨H.subtype ⁻¹' S.sets (max m n),⟨max m n,rfl⟩,?_⟩
    intro x hx
    exact ⟨S.antitone (le_max_left _ _) hx,S.antitone (le_max_right _ _) hx⟩
  one' := by rintro U ⟨n,rfl⟩; exact S.one_mem n
  mul' := by
    rintro U ⟨n,rfl⟩
    refine ⟨H.subtype ⁻¹' S.sets (n+1),⟨n+1,rfl⟩,?_⟩
    rintro x ⟨a,ha,b,hb,rfl⟩
    apply S.sq_subset n
    rw [pow_two]
    exact Set.mul_mem_mul ha hb
  inv' := by
    rintro U ⟨n,rfl⟩
    refine ⟨H.subtype ⁻¹' S.sets n,⟨n,rfl⟩,?_⟩
    intro x hx
    have hi : (x.val)⁻¹ ∈ (S.sets n)⁻¹ := by simpa using hx
    change (x.val)⁻¹ ∈ S.sets n
    simpa only [S.inv_eq n] using hi
  conj' := by
    rintro g U ⟨n,rfl⟩
    obtain ⟨m,hm⟩ := (hH g.property).1 n
    refine ⟨H.subtype ⁻¹' S.sets m,⟨m,rfl⟩,?_⟩
    exact fun x hx => hm x.val hx

end ShrinkingGroupNeighbourhoods
end DirectedCycles
