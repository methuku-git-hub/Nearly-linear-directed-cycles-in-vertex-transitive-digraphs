import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
namespace DirectedCycles

/-- Selecting a representative from each nonempty cell of a finite cover
keeps the covering cardinal bound and puts every representative in A. -/
theorem finite_cover_representatives {X I : Type*} [Nonempty X]
    (F : Finset I) (A : Set X) (R : I → X → Prop)
    (hcover : ∀ x ∈ A, ∃ i ∈ F, R i x) :
    ∃ T : Finset X, (T : Set X) ⊆ A ∧ T.card ≤ F.card ∧
      ∀ x ∈ A, ∃ y ∈ T, ∃ i ∈ F, R i x ∧ R i y := by
  classical
  let J := F.filter (fun i => ∃ x ∈ A, R i x)
  have hex : ∀ i : I, ∃ x : X, i ∈ J → x ∈ A ∧ R i x := by
    intro i
    by_cases hi : i ∈ J
    · obtain ⟨x,hx,hr⟩ := (Finset.mem_filter.mp hi).2
      exact ⟨x,fun _ => ⟨hx,hr⟩⟩
    · exact ⟨Classical.choice inferInstance,fun h => (hi h).elim⟩
  choose f hf using hex
  refine ⟨J.image f,?_,Finset.card_image_le.trans (Finset.card_filter_le _ _),?_⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact (hf i hi).1
  · intro x hx
    obtain ⟨i,hi,hr⟩ := hcover x hx
    have hiJ : i ∈ J := Finset.mem_filter.mpr ⟨hi,x,hx,hr⟩
    exact ⟨f i,Finset.mem_image.mpr ⟨i,hiJ,rfl⟩,i,hi,hr,(hf i hiJ).2⟩
end DirectedCycles
