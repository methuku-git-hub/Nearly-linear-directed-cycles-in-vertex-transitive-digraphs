module

public import DirectedCycles.AbelianShortGeneration
public import Mathlib.GroupTheory.Abelianization.Defs

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- The abelian inverse input produces a subgroup and a uniformly bounded
list of generators in the abelianization, with actual lifts in A^4. -/
theorem abelianization_short_generators (hAb : FiniteAbelianShortGeneration)
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ r : ℕ, ∀ (G : Type) [Group G] [Finite G] (A : Set G),
      IsApproximateSubgroup K A → Subgroup.closure A = ⊤ →
      ∃ (H : Subgroup (Abelianization G)) (k : ℕ) (x : Fin k → G),
        k ≤ r ∧ (H : Set (Abelianization G)) ⊆ Abelianization.of '' (A^4) ∧
        (∀ i, x i ∈ A^4) ∧
        Subgroup.closure ((H : Set (Abelianization G)) ∪
          Set.range (fun i => Abelianization.of (x i))) = ⊤ := by
  classical
  obtain ⟨r,hstructure⟩ := hAb K hK
  refine ⟨r,?_⟩
  intro G _ _ A hA hgen
  let π : G →* Abelianization G := Abelianization.of
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective (commutator G)
  let : Finite (Abelianization G) := Finite.of_surjective π hπ
  have hπgen := image_generating_set π hπ A hgen
  obtain ⟨H,F,hH,hF,hcard,hgenerate⟩ := hstructure (Abelianization G) (π '' A) (hA.image π) hπgen
  rw [← Set.image_pow] at hH hF
  have hlift : ∀ a : F, ∃ g ∈ A^4, π g = a.val := fun a => hF a.property
  choose l hl he using hlift
  let e := Fintype.equivFin F
  let x := fun i : Fin (Fintype.card F) => l (e.symm i)
  have hrange : Set.range (fun i => π (x i)) = (F : Set (Abelianization G)) := by
    ext a
    constructor
    · rintro ⟨i,rfl⟩
      change π (x i) ∈ F
      rw [show π (x i) = (e.symm i).val from he (e.symm i)]
      exact (e.symm i).property
    · intro ha
      refine ⟨e ⟨a,ha⟩,?_⟩
      change π (l (e.symm (e ⟨a,ha⟩))) = a
      rw [e.symm_apply_apply]
      exact he ⟨a,ha⟩
  refine ⟨H,Fintype.card F,x,by simpa using hcard,hH,fun i => hl (e.symm i),?_⟩
  change Subgroup.closure ((H : Set (Abelianization G)) ∪ Set.range (fun i => π (x i))) = ⊤
  rw [hrange]
  exact hgenerate

end DirectedCycles
