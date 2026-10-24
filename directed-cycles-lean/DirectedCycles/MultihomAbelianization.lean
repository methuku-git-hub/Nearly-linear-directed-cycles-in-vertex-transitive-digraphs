import DirectedCycles.GroupMultihomOperations
import Mathlib.GroupTheory.Abelianization.Defs

set_option autoImplicit false
namespace DirectedCycles

/-- Equality under all one-coordinate replacements implies equality on a
finite product, with the other coordinates allowed to vary arbitrarily. -/
theorem finite_function_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ι → Type*} {C : Type*} (f : (∀ i, B i) → C) (x y : ∀ i, B i)
    (h : ∀ z i, f (Function.update z i (x i)) = f (Function.update z i (y i))) :
    f x = f y := by
  classical
  have hh : ∀ s : Finset ι, f x = f (fun i => if i ∈ s then y i else x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      let z := fun j => if j ∈ s then y j else x j
      have hz : Function.update z i (x i) = z := by
        have he : z i = x i := by simp [z,hi]
        rw [← he,Function.update_eq_self]
      have ht := h z i
      rw [hz] at ht
      calc
        f x = f z := ih
        _ = f (Function.update z i (y i)) := ht
        _ = f (fun j => if j ∈ insert i s then y j else x j) := by
          congr 1
          funext j
          by_cases hji : j = i
          · subst j; simp
          · simp [z,hji]
  simpa using hh Finset.univ

namespace GroupMultihom
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {B : ι → Type*} [∀ i, Group (B i)] {G : Type*} [CommGroup G]

theorem eq_of_abelianization_eq (φ : GroupMultihom B G) (x y : ∀ i, B i)
    (hxy : ∀ i, Abelianization.of (x i) = Abelianization.of (y i)) : φ x = φ y := by
  apply finite_function_congr φ x y
  intro z i
  let f := Abelianization.lift (φ.slice z i)
  have hh := congrArg f (hxy i)
  exact hh

noncomputable def abelianizationDom (φ : GroupMultihom B G) :
    GroupMultihom (fun i => Abelianization (B i)) G := by
  classical
  let t : ∀ i, Abelianization (B i) → B i := fun i q =>
    Classical.choose (QuotientGroup.mk'_surjective (commutator _) q)
  have ht : ∀ i q, Abelianization.of (t i q) = q :=
    fun i q => Classical.choose_spec (QuotientGroup.mk'_surjective (commutator _) q)
  refine ⟨fun x => φ (fun i => t i (x i)),?_,?_⟩
  · intro x i
    have he : φ (fun j => t j (Function.update x i 1 j)) =
        φ (Function.update (fun j => t j (x j)) i 1) := by
      apply eq_of_abelianization_eq
      intro j
      by_cases hji : j = i
      · subst j; simp [ht]
      · simp [hji]
    exact he.trans (φ.map_one _ i)
  · intro x i a b
    have he : ∀ u v, Abelianization.of v = u →
        φ (fun j => t j (Function.update x i u j)) =
          φ (Function.update (fun j => t j (x j)) i v) := by
      intro u v hv
      apply eq_of_abelianization_eq
      intro j
      by_cases hji : j = i
      · subst j; simpa [ht] using hv.symm
      · simp [hji]
    rw [he (a*b) (t i a*t i b) (by rw [_root_.map_mul,ht,ht]),
      he a (t i a) (ht i a),he b (t i b) (ht i b),φ.map_mul]

theorem abelianizationDom_apply_of (φ : GroupMultihom B G) (x : ∀ i, B i) :
    φ.abelianizationDom (fun i => Abelianization.of (x i)) = φ x := by
  change φ (fun i => Classical.choose (QuotientGroup.mk'_surjective (commutator _) (Abelianization.of (x i)))) = φ x
  apply eq_of_abelianization_eq
  intro i
  exact Classical.choose_spec (QuotientGroup.mk'_surjective (commutator _) (Abelianization.of (x i)))

theorem abelianizationDom_range (φ : GroupMultihom B G) :
    Set.range φ.abelianizationDom = Set.range φ := by
  ext g
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨fun i => Classical.choose (QuotientGroup.mk'_surjective (commutator _) (x i)),rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨fun i => Abelianization.of (x i),φ.abelianizationDom_apply_of x⟩

end GroupMultihom
end DirectedCycles
