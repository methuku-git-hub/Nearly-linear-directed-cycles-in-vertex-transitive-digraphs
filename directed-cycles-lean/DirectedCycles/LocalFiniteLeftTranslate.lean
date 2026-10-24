import DirectedCycles.LocalTranslateEnergy

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

noncomputable def leftTranslate (B : Finset G) (g : G) : Finset G := by
  classical
  exact L.finsetMul {g} B

theorem mem_leftTranslate (B : Finset G) (g x : G) :
    x ∈ L.leftTranslate B g ↔ ∃ b ∈ B, L.mulRel g b x := by
  classical
  simp only [leftTranslate,L.mem_finsetMul,Finset.mem_singleton,exists_eq_left]

theorem card_leftTranslate (hc : L.Cancellative) (B : Finset G) (g : G)
    (hdom : ∀ b ∈ B, L.Defined g b) : (L.leftTranslate B g).card = B.card := by
  classical
  symm
  apply Finset.card_bij (fun b hb => L.mul g b (hdom b hb))
  · intro b hb
    exact (L.mem_leftTranslate B g _).2 ⟨b,hb,L.mul_spec _ _ _⟩
  · intro a ha b hb he
    have hm := L.mul_spec g a (hdom a ha)
    rw [he] at hm
    exact hc.left_cancel hm (L.mul_spec g b (hdom b hb))
  · intro x hx
    obtain ⟨b,hb,hm⟩ := (L.mem_leftTranslate B g x).1 hx
    exact ⟨b,hb,L.unique (L.mul_spec _ _ _) hm⟩
end LocalGroupAlgebra
end DirectedCycles
