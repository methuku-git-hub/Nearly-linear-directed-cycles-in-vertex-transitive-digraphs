module

public import DirectedCycles.FiniteConstraints

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A finite family of forbidden differences can be satisfied whenever
the sum of the forbidden-set sizes incident to each variable is smaller
than the ambient group. Multiple constraints on the same pair are allowed. -/
theorem finite_difference_assignment {I C A : Type*} [Fintype I] [Fintype C]
    [Fintype A] [AddCommGroup A] [DecidableEq I]
    (src dst : C → I) (bad : C → Finset A) (hne : ∀ c, src c ≠ dst c)
    (hbudget : ∀ i, (∑ c, if src c = i ∨ dst c = i then (bad c).card else 0) < Fintype.card A) :
    ∃ v : I → A, ∀ c, v (dst c) - v (src c) ∉ bad c := by
  classical
  let forbidden := fun (i : I) (f : I → A) (c : C) =>
    if src c = i then (bad c).image (fun d => f (dst c) - d)
    else if dst c = i then (bad c).image (fun d => d + f (src c)) else ∅
  have hchoose : ∀ i (f : I → A), ∃ a, ∀ c, a ∉ forbidden i f c := by
    intro i f
    let F := Finset.univ.biUnion (forbidden i f)
    have hcard : F.card < Fintype.card A := by
      apply Finset.card_biUnion_le.trans_lt
      apply lt_of_le_of_lt _ (hbudget i)
      apply Finset.sum_le_sum
      intro c _
      by_cases hs : src c = i
      · simpa only [forbidden,ite_eq_left hs,hs,true_or,ite_true] using
          (Finset.card_image_le (s := bad c) (f := fun d => f (dst c) - d))
      · by_cases ht : dst c = i
        · simpa only [forbidden,ite_eq_right hs,ht,or_true,ite_true] using
            (Finset.card_image_le (s := bad c) (f := fun d => d + f (src c)))
        · simp [forbidden,hs,ht]
    obtain ⟨a,ha⟩ : ∃ a : A, a ∉ F := by
      by_contra he
      push Not at he
      have hh := Finset.eq_univ_of_forall he
      rw [hh,Finset.card_univ] at hcard
      exact (lt_irrefl _ hcard)
    exact ⟨a,fun c hc => ha (Finset.mem_biUnion.mpr ⟨c,Finset.mem_univ c,hc⟩)⟩
  have hpartial : ∀ s : Finset I, ∃ v : I → A,
      ∀ c, src c ∈ s → dst c ∈ s → v (dst c) - v (src c) ∉ bad c := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => 0,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨f,hf⟩ := ih
      obtain ⟨a,ha⟩ := hchoose i f
      let v := Function.update f i a
      have hvi : v i = a := Function.update_self _ _ _
      have hvj : ∀ j, j ≠ i → v j = f j := fun j hj => Function.update_of_ne hj _ _
      refine ⟨v,?_⟩
      intro c hs ht hb
      by_cases hsi : src c = i
      · have hti : dst c ≠ i := fun he => hne c (hsi.trans he.symm)
        rw [hsi,hvi,hvj _ hti] at hb
        apply ha c
        simp only [forbidden,ite_eq_left hsi]
        exact Finset.mem_image.mpr ⟨f (dst c)-a,hb,sub_sub_cancel _ _⟩
      · by_cases hti : dst c = i
        · rw [hti,hvi,hvj _ hsi] at hb
          apply ha c
          simp only [forbidden,ite_eq_right hsi,ite_eq_left hti]
          exact Finset.mem_image.mpr ⟨a-f (src c),hb,sub_add_cancel _ _⟩
        · rw [hvj _ hsi,hvj _ hti] at hb
          exact hf c ((Finset.mem_insert.mp hs).resolve_left hsi)
            ((Finset.mem_insert.mp ht).resolve_left hti) hb
  obtain ⟨v,hv⟩ := hpartial Finset.univ
  exact ⟨v,fun c => hv c (Finset.mem_univ _) (Finset.mem_univ _)⟩

end DirectedCycles
