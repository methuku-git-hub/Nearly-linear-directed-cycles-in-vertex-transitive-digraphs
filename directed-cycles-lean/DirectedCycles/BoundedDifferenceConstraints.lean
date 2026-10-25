module

public import DirectedCycles.DifferenceConstraints

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

theorem incident_forbidden_budget_le {I C A : Type*} [Fintype C] [DecidableEq I]
    (src dst : C → I) (bad : C → Finset A) (i : I) (d w : ℕ)
    (hcard : ∀ c, (bad c).card ≤ w)
    (hdegree : (Finset.univ.filter (fun c => src c = i ∨ dst c = i)).card ≤ d) :
    (∑ c, if src c = i ∨ dst c = i then (bad c).card else 0) ≤ d*w := by
  classical
  rw [← Finset.sum_filter]
  calc (∑ c ∈ Finset.univ.filter (fun c => src c = i ∨ dst c = i), (bad c).card)
      ≤ ∑ _c ∈ Finset.univ.filter (fun c => src c = i ∨ dst c = i), w :=
        Finset.sum_le_sum (fun c _ => hcard c)
    _ ≤ d*w := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact Nat.mul_le_mul_right w hdegree

theorem permutation_incident_card_le_two {I : Type*} [Fintype I] [DecidableEq I]
    (σ : Equiv.Perm I) (i : I) :
    (Finset.univ.filter (fun j => σ j = i ∨ j = i)).card ≤ 2 := by
  apply le_trans (Finset.card_le_card (show
      Finset.univ.filter (fun j => σ j = i ∨ j = i) ⊆ {σ.symm i,i} from ?_))
  · simpa only [Finset.card_singleton] using Finset.card_insert_le (σ.symm i) {i}
  · intro j hj
    rcases (Finset.mem_filter.mp hj).2 with hj | hj
    · have he : j = σ.symm i := by apply σ.injective; simpa using hj
      simp [he]
    · simp [hj]

theorem two_family_difference_assignment {I C E A : Type*} [Fintype I]
    [Fintype C] [Fintype E] [Fintype A] [AddCommGroup A] [DecidableEq I]
    (src₁ dst₁ : C → I) (src₂ dst₂ : E → I)
    (bad₁ : C → Finset A) (bad₂ : E → Finset A) (d₁ d₂ w₁ w₂ : ℕ)
    (hne₁ : ∀ c, src₁ c ≠ dst₁ c) (hne₂ : ∀ c, src₂ c ≠ dst₂ c)
    (hc₁ : ∀ c, (bad₁ c).card ≤ w₁) (hc₂ : ∀ c, (bad₂ c).card ≤ w₂)
    (hd₁ : ∀ i, (Finset.univ.filter (fun c => src₁ c = i ∨ dst₁ c = i)).card ≤ d₁)
    (hd₂ : ∀ i, (Finset.univ.filter (fun c => src₂ c = i ∨ dst₂ c = i)).card ≤ d₂)
    (hb : d₁*w₁+d₂*w₂ < Fintype.card A) :
    ∃ v : I → A, (∀ c, v (dst₁ c)-v (src₁ c) ∉ bad₁ c) ∧
      (∀ c, v (dst₂ c)-v (src₂ c) ∉ bad₂ c) := by
  classical
  let src := Sum.elim src₁ src₂
  let dst := Sum.elim dst₁ dst₂
  let bad := Sum.elim bad₁ bad₂
  obtain ⟨v,hv⟩ := finite_difference_assignment src dst bad (by
    intro c; cases c with
    | inl c => exact hne₁ c
    | inr c => exact hne₂ c) (by
      intro i
      rw [Fintype.sum_sum_type]
      exact (Nat.add_le_add (incident_forbidden_budget_le src₁ dst₁ bad₁ i d₁ w₁ hc₁ (hd₁ i))
        (incident_forbidden_budget_le src₂ dst₂ bad₂ i d₂ w₂ hc₂ (hd₂ i))).trans_lt hb)
  exact ⟨v,fun c => hv (Sum.inl c),fun c => hv (Sum.inr c)⟩

end DirectedCycles
