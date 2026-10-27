module

public import DirectedCycles.LocalApproximateGroups

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

/-- A partial functional multiplication produces at most one value for each
ordered pair, so its image has the usual product cardinal bound. -/
theorem card_setMul_le (A B : Finset G) :
    Nat.card (L.setMul (A : Set G) (B : Set G)) ≤ A.card*B.card := by
  classical
  let S := L.setMul (A : Set G) (B : Set G)
  have hc : ∀ z : S, ∃ a : A, ∃ b : B, L.mulRel a.val b.val z.val := by
    intro z
    obtain ⟨a,ha,b,hb,hm⟩ := z.property
    exact ⟨⟨a,ha⟩,⟨b,hb⟩,hm⟩
  choose a b hab using hc
  let f : S → A × B := fun z => (a z,b z)
  have hf : Function.Injective f := by
    intro x y he
    have ha : a x = a y := congrArg Prod.fst he
    have hb : b x = b y := congrArg Prod.snd he
    have hm := hab x
    rw [ha,hb] at hm
    exact Subtype.ext (L.unique hm (hab y))
  have hh := Nat.card_le_card_of_injective f hf
  change Nat.card (L.setMul (A : Set G) (B : Set G)) ≤ Nat.card (A × B) at hh
  rw [Nat.card_prod] at hh
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hh
end LocalGroupAlgebra

/-- Every finite local approximate group has the corresponding doubling
bound; the proof counts actual defined products. -/
theorem local_approximate_doubling {G : Type*} [Fintype G] {L : LocalGroupAlgebra G}
    {K : ℕ} {A : Finset G} (hA : IsLocalFiniteApproximateGroup L K A) :
    Nat.card (L.wordPower (A : Set G) 2) ≤ K*A.card := by
  classical
  obtain ⟨X,hX,_,_,hcover⟩ := hA.cover
  have hsub := Nat.card_le_card_of_injective (Set.inclusion hcover) (Set.inclusion_injective hcover)
  exact hsub.trans ((L.card_setMul_le X A).trans (Nat.mul_le_mul_right A.card hX))
end DirectedCycles
