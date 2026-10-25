module

public import DirectedCycles.NilpotentRanks

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A subgroup image is a quotient of any specified quotient through
which the homomorphism factors. -/
theorem subgroup_image_quotient_surjection {G A : Type*} [Group G] [Group A]
    (f : G →* A) (N H : Subgroup G) [H.Normal]
    (hH : H ≤ f.ker) :
    ∃ q : (N ⧸ H.comap N.subtype) →* N.map f, Function.Surjective q := by
  let p := f.subgroupMap N
  have hker : H.comap N.subtype ≤ p.ker := by
    intro g hg
    apply Subtype.ext
    exact hH hg
  let q := QuotientGroup.lift (H.comap N.subtype) p hker
  refine ⟨q,?_⟩
  intro y
  obtain ⟨x,hx⟩ := f.subgroupMap_surjective N y
  exact ⟨QuotientGroup.mk x,hx⟩

/-- Nilpotence, rank and class survive the actual induced image. -/
theorem nilpotent_image_quotient_bounds {G A : Type*} [Group G] [Group A] [Finite G] [Finite A]
    (f : G →* A) (N H : Subgroup G) [H.Normal]
    [Group.IsNilpotent (N ⧸ H.comap N.subtype)] (hH : H ≤ f.ker) :
    Group.IsNilpotent (N.map f) ∧
    Group.rank (N.map f) ≤ Group.rank (N ⧸ H.comap N.subtype) ∧
    Group.nilpotencyClass (N.map f) ≤ Group.nilpotencyClass (N ⧸ H.comap N.subtype) := by
  obtain ⟨q,hq⟩ := subgroup_image_quotient_surjection f N H hH
  exact ⟨Group.nilpotent_of_surjective q hq,Group.rank_le_of_surjective q hq,
    Group.nilpotencyClass_le_of_surjective q hq⟩

end DirectedCycles
