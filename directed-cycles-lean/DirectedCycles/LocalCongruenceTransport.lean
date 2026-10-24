import DirectedCycles.LocalGroupCongruence
import DirectedCycles.SurjectiveKernelEquiv

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupCongruence
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}
    (C : LocalGroupCongruence L) (D : LocalGroupCongruence M) (e : G ≃ H)
    (hrel : ∀ a b, C.toSetoid.r a b ↔ D.toSetoid.r (e a) (e b))

/-- Transporting the actual equivalence relation along an equivalence of
carriers induces an equivalence of the actual quotient carriers. -/
noncomputable def transportEquiv : C.Carrier ≃ D.Carrier :=
  surjectiveKernelEquiv C.project (D.project ∘ e) Quotient.mk_surjective
    (Quotient.mk_surjective.comp e.surjective) (by
      intro a b
      exact Quotient.eq.trans ((hrel a b).trans Quotient.eq.symm))

theorem transportEquiv_project (a : G) :
    transportEquiv C D e hrel (C.project a) = D.project (e a) :=
  surjectiveKernelEquiv_apply _ _ _ _ _ a

/-- Exact multiplication-domain equivalence survives quotient transport. -/
theorem transportEquiv_mul_iff
    (he : ∀ a b c, L.mulRel a b c ↔ M.mulRel (e a) (e b) (e c)) (x y z : C.Carrier) :
    C.algebra.mulRel x y z ↔ D.algebra.mulRel
      (transportEquiv C D e hrel x) (transportEquiv C D e hrel y) (transportEquiv C D e hrel z) := by
  constructor
  · rintro ⟨a,b,c,rfl,rfl,rfl,hm⟩
    rw [transportEquiv_project,transportEquiv_project,transportEquiv_project]
    exact ⟨e a,e b,e c,rfl,rfl,rfl,(he a b c).1 hm⟩
  · intro hm
    obtain ⟨a,rfl⟩ := Quotient.exists_rep x
    obtain ⟨b,rfl⟩ := Quotient.exists_rep y
    obtain ⟨c,rfl⟩ := Quotient.exists_rep z
    rw [transportEquiv_project,transportEquiv_project,transportEquiv_project] at hm
    obtain ⟨d,hd,hm'⟩ := D.lift_mul hm
    refine ⟨a,b,e.symm d,rfl,rfl,?_,?_⟩
    · apply Quotient.sound
      apply (hrel _ _).2
      rw [e.apply_symm_apply]
      exact Quotient.exact hd
    · apply (he _ _ _).2
      simpa only [e.apply_symm_apply] using hm'
end LocalGroupCongruence
end DirectedCycles
