module

public import DirectedCycles.InternalFiniteSetFamily
public import DirectedCycles.OpenSubgroupGoodModel

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]
    {S : Type*} [Group S]

/-- Relative internality along an actual source embedding. This formulation
retains arbitrary nested source subgroup restrictions without assuming that
the restricted subgroup itself is internal. -/
def IsInternalFiniteAlong (e : S →* GroupUltraproduct (U : Filter ι) G) (T : Set S) : Prop :=
  ∃ B : ∀ i, Finset (G i), T = e ⁻¹' ultraSet (U : Filter ι) G (fun i => (B i : Set (G i)))

theorem restricted_internal_finite_along
    (e : S →* GroupUltraproduct (U : Filter ι) G) (H : Subgroup S) (T : Set H) :
    RestrictedInternal H (IsInternalFiniteAlong U G e) T ↔
      IsInternalFiniteAlong U G (e.comp H.subtype) T := by
  constructor
  · rintro ⟨B,⟨B',rfl⟩,hB'⟩
    exact ⟨B',hB'.symm⟩
  · rintro ⟨B',rfl⟩
    exact ⟨e ⁻¹' ultraSet (U : Filter ι) G (fun i => (B' i : Set (G i))),⟨B',rfl⟩,rfl⟩

theorem internal_finite_in_iff_along (H : Subgroup (GroupUltraproduct (U : Filter ι) G))
    (T : Set H) : IsInternalFiniteIn U G H T ↔ IsInternalFiniteAlong U G H.subtype T := Iff.rfl
end DirectedCycles
